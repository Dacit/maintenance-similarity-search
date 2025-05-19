/* Author: Fabian Huch, TU Muenchen

Clone detection for Isabelle theories.
 */
package isabelle


import isabelle.Document.Snapshot
import isabelle.find_facts.Thy_Blocks

import java.io.{BufferedInputStream, BufferedOutputStream, FileInputStream, FileOutputStream,
  InputStream, OutputStream}

import scala.annotation.tailrec
import scala.collection.mutable
import scala.jdk.CollectionConverters._

import com.github.luben.zstd


object Clone_Detect {
  def min[A](args: A*)(implicit ordering: Ordering[A]) = args.min

  val name_blacklisted =
    Set(
      "cases", "elims", "induct", "pelims", "simps", "pinduct", "psimps", "inducts", "intros",
      "case", "case_cong", "case_cong_weak", "case_distrib", "case_transfer", "eq.refl", "eq.simps",
      "exhaust", "nchotomy", "rec", "rec_transfer", "size", "size_gen", "split", "split_asm",
      "splits")

  @tailrec def base(s: String): String =
    if (!Long_Name.is_qualified(s)) s
    else{
      val s1 = Long_Name.base_name(s)
      if (name_blacklisted(s1)) s else base(s1)
    }


  /* character-wise comparisons */

  object Chars {
    val range = ((0 until 128).map(_.toChar) ++ Symbol.symbols.entries.flatMap(_.symbol)).distinct
  }

  case class Chars(s: String) {
    private val chars_count: Array[Int] = {
      val freqs = s.groupMapReduce(identity)(_ => 1)(_ + _).withDefaultValue(0)
      (for(key <- Chars.range) yield freqs(key)).toArray
    }

    val length = s.length

    def distance(that: Chars, approx: Boolean = false): Int =
      if (this.s == "") that.length
      else if (that.s == "") this.length
      else if (!approx) {
        def fill(j: Int, i: Int): Int = if (i == 0) j else if (j == 0) i else 0
        val d = Array.tabulate(that.length + 1, this.length + 1)(fill)

        for {
          j <- 1 until that.length
          i <- 1 until this.length
        } {
          d(j)(i) =
            if (this.s(i) == that.s(j)) d(j - 1)(i - 1)
            else min(d(j - 1)(i) + 1, d(j)(i - 1) + 1, d(j - 1)(i - 1) + 1)
        }

        d(that.length)(this.length)
      }
      else {
        val max = Math.max(this.length, that.length)
        var shared = 0
        for (key <- Chars.range) {
          shared += Math.min(chars_count(key), that.chars_count(key))
        }
        max - shared
      }

    def compare(that: Chars, approx: Boolean = false): Double = {
      val rel_dist = 
        if (s == "" && that.s == "") 0.0
        else distance(that, approx = approx).toDouble / Math.max(s.length, that.s.length).toDouble
      1.0 - rel_dist
    }
  }


  /* term comparison by constrained edit distance of unordered HNF trees */

  sealed trait Head { def distance: Head => Double }

  object Head {
    def t_eq_vars(t1: Term.Typ, t2: Term.Typ): Boolean =
      (t1, t2) match {
        case (Term.TFree(_, sort1), Term.TFree(_, sort2)) => sort1 == sort2
        case (Term.TVar(_, sort1), Term.TVar(_, sort2)) => sort1 == sort2
        case (Term.Type(name1, args1), Term.Type(name2, args2)) =>
          if (name1 != name2 || args1.length != args2.length) false
          else args1.zip(args2).forall(t_eq_vars)
        case _ => false
      }

    case class Free(id: Int, typ: Term.Typ) extends Head {
      def distance: Head => Double = {
        case Free(id2, typ2) if id == id2 && t_eq_vars(typ, typ2) => 0.1
        case Free(_, typ2) if typ == typ2 => 0.3
        case Free(_, typ2) if t_eq_vars(typ, typ2) => 0.5
        case _: Free => 0.7
        case _: Const => 0.8
        case _ => 1.0
      }
    }

    case class Bound(idx: Int, typ: Term.Typ) extends Head {
      def distance: Head => Double = {
        case Bound(idx2, typ2) if idx == idx2 && t_eq_vars(typ, typ2) => 0.1
        case Bound(_, typ2) if typ == typ2 => 0.4
        case Bound(_, typ2) if t_eq_vars(typ, typ2) => 0.6
        case _: Bound => 0.7
        case _ => 1.0
      }
    }

    case class Const(name: String, typargs: List[Term.Typ]) extends Head {
      def typargs_dist(typargs2: List[Term.Typ]): Double = {
        def typ_dist(typ1: Term.Typ, typ2: Term.Typ): Double =
          if (typ1 == typ2) 0.0 else if (t_eq_vars(typ1, typ2)) 0.5 else 1.0
        (typargs.zip(typargs2).map(typ_dist).sum + (typargs.length - typargs2.length).abs.toDouble)
          / typargs.length.toDouble
      }

      def distance: Head => Double = {
        case Const(name2, typargs2) if name == name2 => 0.2 * typargs_dist(typargs2)
        case Const(_, typargs2) => 0.7 + 0.2 * typargs_dist(typargs2)
        case _ => 1.0
      }
    }

    def distance(l: Option[Head], r: Option[Head]) =
      (l, r) match {
        case (Some(l), Some(r)) => if (l == r) 0.0 else l.distance(r)
        case _ => 1.0
      }
  }

  case class HNF_Term(hd: Head, args: Vector[HNF_Term]) {
    lazy val nodes: Vector[HNF_Term] = this +: args.flatMap(_.nodes)

    def edges(start: Int): Vector[Int] =
      args.foldLeft((Vector.empty[Int], start)) {
        case ((res, start), arg) => (res :+ (start + 1), start + arg.nodes.length)
      }._1

    def edgess(res: Vector[Vector[Int]] = Vector.empty): Vector[Vector[Int]] =
      args.foldLeft(res :+ edges(res.length)) { case (res, arg) => arg.edgess(res) }
  }

  object HNF_Term {
    def build(t: Term.Term): HNF_Term = {
      import Term.*

      def frees(t: Term.Term): List[Free] =
        t match {
          case f: Free => List(f)
          case Abs(_, _, body) => frees(body)
          case App(fun, arg) => frees(fun) ::: frees(arg)
          case _ => Nil
        }

      val free_ids = frees(t).distinct.groupBy(_.typ)

      def split_abs(t: Term.Term): (List[Abs], Term.Term) =
        t match {
          case Abs(name, typ, body) =>
            val (res, t) = split_abs(body)
            (Abs(name, typ, dummy) :: res, t)
          case _ => (Nil, t)
        }

      def split_apps(t: Term.Term): List[Term.Term] =
        t match {
          case App(fun, arg) => split_apps(fun) ::: List(arg)
          case _ => List(t)
        }

      def build(t: Term.Term, stk: List[Abs]): HNF_Term = {
        val (abs, t1) = split_abs(t)
        val stk1 = abs.reverse ::: stk
        val args = split_apps(t1)

        val hd =
          args.head match {
            case Term.Const(name, typargs) => Head.Const(name, typargs)
            case OFCLASS(typ, name) => Head.Const(name + "_class", List(typ))
            case f@Free(name, typ) => Head.Free(free_ids(typ).indexOf(f), typ)
            case Bound(index) =>
              val typ = stk1(index).typ
              Head.Bound(stk1.take(index).count(_.typ == typ), typ)
            case e => error("Invalid element: " + e)
          }

        HNF_Term(hd, args.tail.map(build(_, stk1)).toVector)
      }

      build(t, Nil)
    }

    // NB: tree distance function by Zhang 1996, Algorithmica,
    // "A constrained edit distance between unordered labeled trees"
    def dist(t1: HNF_Term, t2: HNF_Term): Double = {
      def dist(t1: Option[HNF_Term], t2: Option[HNF_Term]): Double =
        Head.distance(t1.map(_.hd), t2.map(_.hd))

      val n1 = t1.nodes.length
      val n2 = t2.nodes.length
      val edges1 = t1.edgess()
      val edges2 = t2.edgess()

      val D_T = Array.fill(n1 + 1, n2 + 1)(0.0)
      val D_F = Array.fill(n1 + 1, n2 + 1)(0.0)
      for (i <- Range(n1 - 1, -1, -1)) {
        D_F(i)(n2) = edges1(i).map(D_T(_)(n2)).sum
        D_T(i)(n2) = D_F(i)(n2) + dist(Some(t1.nodes(i)), None)
      }
      for (j <- Range(n2 - 1, -1, -1)) {
        D_F(n1)(j) = edges2(j).map(D_T(n1)(_)).sum
        D_T(n1)(j) = D_F(n1)(j) + dist(None, Some(t2.nodes(j)))
      }

      for {
        i <- Range(n1 - 1, -1, -1)
        j <- Range(n2 - 1, -1, -1)
      } {
        val e1_i = edges1(i).length
        val e2_j = edges2(j).length

        D_F(i)(j) =
          if (e1_i == 0) D_F(n1)(j)
          else if (e2_j == 0) D_F(i)(n2)
          else min(
            D_F(n1)(j) + edges2(j).map(j_t => D_F(i)(j_t) - D_F(n1)(j_t)).min,
            D_F(i)(n2) + edges1(i).map(i_s => D_F(i_s)(j) - D_F(i_s)(n2)).min,
            if (e1_i == 1) {
              val i_0 = edges1(i)(0)
              D_F(n1)(j) + edges2(j).map(j_t => D_T(i_0)(j_t) - D_T(n1)(j_t)).min
            }
            else if (e2_j == 1) {
              val j_0 = edges2(j)(0)
              D_F(i)(n2) + edges1(i).map(i_s => D_T(i_s)(j_0) - D_T(i_s)(n2)).min
            }
            else {
              def fill(k: Int, l: Int): Double =
                if (k < e1_i && l < e2_j) D_T(edges1(i)(k))(edges2(j)(l))
                else if (k < e1_i) if (l == k + e2_j) D_T(edges1(i)(k))(n2) else Double.MaxValue
                else if (l < e2_j) if (k == l + e1_i) D_T(n1)(edges2(j)(l)) else Double.MaxValue
                else 0.0
              val matrix = Array.tabulate(e1_i + e2_j, e1_i + e2_j)(fill)

              (for ((task, worker) <- new HungarianAlgorithm(matrix).execute().zipWithIndex)
               yield matrix(worker)(task)).sum
            })

        D_T(i)(j) =
          min(
            if (e2_j == 0) D_T(i)(n2)
            else D_T(n1)(j) + edges2(j).map(j_t => D_T(i)(j_t) - D_T(n1)(j_t)).min,
            if (e1_i == 0) D_T(n1)(j)
            else D_T(i)(n2) + edges1(i).map(i_s => D_T(i_s)(j) - D_T(i_s)(n2)).min,
            D_F(i)(j) + dist(Some(t1.nodes(i)), Some(t2.nodes(j))))
      }

      D_T(0)(0)
    }
  }

  /* max-weight matching of tokens between two spans */

  object Matching {
    def size_score(span1: Span, span2: Span, uncategorized: Boolean = false): Double = {
      val total =
        if (uncategorized) {
          val min_length = Math.min(span1.token_length, span2.token_length)
          Math.min(span1.token_relevance_accum(min_length), span2.token_relevance_accum(min_length))
        }
        else if (span1.categories.length > span2.categories.length) {
          size_score(span2, span1, uncategorized = uncategorized)
        }
        else {
          var res = 0.0
          span1.categorized_relevance_accum.foreach {
            case (category, accum1) =>
              val accum2 = span2.categorized_relevance_accum.get(category)
              if (accum2.isDefined) {
                val min_length = Math.min(accum1.length, accum2.get.length) - 1
                res = res + Math.min(accum1(min_length), accum2.get(min_length))
              }
          }
          res
        }
      total / Math.max(span1.relevance, span2.relevance)
    }

    def apply(
      span1: Span,
      span2: Span,
      approx: Boolean = false,
      relaxed: Boolean = false
    ): Matching =
      if (span1.categories.length > span2.categories.length) apply(span2, span1, approx, relaxed)
      else {
        var sum = 0.0
        span1.categorized.foreach {
          case (category, tokens1) =>
            val tokens2 = span2.categorized.get(category)
            if (tokens2.isDefined) {
              if (relaxed) {
                tokens1.foreach { token1 =>
                  sum = sum + tokens2.get.map(Token.score(token1, _, approx)).max
                }
              }
              // NB: solve max-weight bipartite mathing via min-cost assignment problem
              else {
                def fill(j: Int, i: Int): Double = -Token.score(tokens1(j), tokens2.get(i), approx)
                val matrix = Array.tabulate(tokens1.length, tokens2.get.length)(fill)
                for {
                  (task, worker) <- new HungarianAlgorithm(matrix).execute().zipWithIndex
                  if task >= 0
                } sum = sum + Token.score(tokens1(worker), tokens2.get(task), approx)
              }
            }
        }
        new Matching(span1, span2, sum / Math.max(span1.relevance, span2.relevance))
    }
  }

  case class Matching(left: Span, right: Span, score: Double) {
    def by_terms(offset: Double = 1.2, size_score: Boolean = false): Matching =
      if (left.terms.isEmpty && right.terms.isEmpty) this
      else if (left.terms.isEmpty || right.terms.isEmpty) copy(score = 0.0)
      else {
        def fill(j: Int, i: Int): Double = {
          val l = left.hnf_terms(j)
          val r = right.hnf_terms(i)
          val dist = 
            if (size_score) (l.nodes.length - r.nodes.length).abs.toDouble else HNF_Term.dist(l, r)
          val score = 1.0 - (dist / (l.nodes.length + r.nodes.length).toDouble)
          -score
        }

        val matrix = Array.tabulate(left.terms.length, right.terms.length)(fill)
        val total = 
          (for {
            (task, worker) <- new HungarianAlgorithm(matrix).execute().zipWithIndex
            if task >= 0
          } yield -matrix(worker)(task)).sum

        val score1 = total / Math.max(left.terms.length, right.terms.length).toDouble
        val score2 = score * (offset + score1) / (1.0 + offset)

        copy(score = score2)
      }
  }


  /* clone class */

  object Clone_Class {
    @tailrec
    def merge(classes: List[Clone_Class]): List[Clone_Class] = {
      val by_span = 
        (for {
          cls <- classes
          span <- cls.spans
        } yield span -> cls).groupMap(_._1)(_._2)
      var updated = Set.empty[Clone_Class]

      val res =
        for {
          cls <- classes
          if !updated.contains(cls)
        } yield {
          val clss = cls.spans.flatMap(by_span(_)).distinct
          updated ++= clss
          new Clone_Class(clss.flatMap(_.rep).distinct)
        }
      if (res == classes) res else merge(res)
    }

    def make(matchings: List[Matching]): List[Clone_Class] =
      merge(matchings.map(List(_)).map(new Clone_Class(_)))
  }

  class Clone_Class private(private val rep: List[Matching]) {
    val spans: List[Span] = rep.flatMap(matching => List(matching.left, matching.right)).distinct

    private val scores = rep.map(_.score)
    val max_score = scores.max
    val min_score = scores.min

    override val hashCode: Int = rep.hashCode()
    override def equals(that: Any): Boolean =
      that match {
        case other: Clone_Class => rep == other.rep
        case _ => false
      }
    override def toString: String = {
      val range =
        if (min_score == max_score) String.format("%.2f", max_score)
        else String.format("%.2f-%.2f", max_score, min_score)

      spans.length.toString + " clones (score: " + range + "): {\n" +
        Library.indent_lines(2, spans.mkString("\n")) + "\n}"
    }
  }

  /* similarity scores on [0,1] interval */

  object Score {
    val same = 1.0
    val almost = 0.9
    val mostly = 0.7
    val similar = 0.5
    val related = 0.2
    val different = 0.0
  }


  /* tokens with distinct syntactic categories */

  object Token {
    def score(t1: Token, t2: Token, approx: Boolean = false): Double = {
      if (t1.category != t2.category) 0.0
      else {
        val similarity =
          (t1, t2) match {
            case (t1: Command.T, t2: Command.T) => t1.category.similarity(t1, t2)
            case (t1: Keyword.T, t2: Keyword.T) => Score.same
            case (t1: Comment.T, t2: Comment.T) => t1.category.similarity(t1, t2, approx = approx)
            case (t1: Str.T, t2: Str.T) => t1.category.similarity(t1, t2, approx = approx)
            case (t1: Term_Var.T, t2: Term_Var.T) => t1.category.similarity(t1, t2, approx = approx)
            case (t1: Typ_Var.T, t2: Typ_Var.T) => t1.category.similarity(t1, t2, approx = approx)
            case (t1: Inner.T, t2: Inner.T) => Score.same
            case (t1: Proof.T, t2: Proof.T) => t1.category.similarity(t1, t2, approx = approx)
            case (t1: Entity.T, t2: Entity.T) => t1.category.similarity(t1, t2)
            case (t1: Unknown.T, t2: Unknown.T) => t1.category.similarity(t1, t2, approx = approx)
            case _ => 0.0
          }
        similarity * t1.category.relevance
      }
    }
  }

  sealed trait Token { def category: Category }

  enum Kind {
    case command, keyword, comment, str, term_var, typ_var, inner, entity, proof, unknown, delete
  }

  object Category {
    val specifity: Ordering[Category] =
      Ordering.by({
        case Unknown("") => 0
        case Unknown(_) => 1
        case Str => 2
        case Inner(_) => 3
        case Entity(_, "") => 4
        case Entity(_, _) => 5
        case Comment => 6
        case Keyword(_) => 7
        case Delete => 9
        case _ => 8
      })
  }

  sealed abstract class Category(kind: Kind) {
    val kind_name = kind.toString
    lazy val relevance: Double =
      this match {
        case _: Command => 3.0
        case _: Keyword => 0.4
        case Comment => 0.5
        case Str => 2.0
        case _: Term_Var => 0.4
        case _: Typ_Var => 0.3
        case _: Inner => 0.2
        case Proof => 4.0
        case _: Entity => 1.0
        case _: Unknown => 0.9
        case _ => 0.0
      }
  }

  object Command { case class T(name: String, category: Command) extends Token }
  case class Command(kind: String) extends Category(Kind.command) {
    override val hashCode = (kind_name, kind).hashCode
    def similarity(t1: Command.T, t2: Command.T): Double =
      if (t1.name == t2.name) Score.same else Score.almost
  }

  object Keyword { case class T(category: Keyword) extends Token }
  case class Keyword(rep: String) extends Category(Kind.keyword) {
    override val hashCode = (kind_name, rep).hashCode
  }

  case object Comment extends Category(Kind.comment) {
    case class T(src: Chars) extends Token { val category: Comment.type = Comment }

    override val hashCode = kind_name.hashCode
    def similarity(t1: Comment.T, t2: Comment.T, approx: Boolean = false): Double =
      Math.max(Score.related, t1.src.compare(t2.src, approx = approx))
  }

  case object Str extends Category(Kind.str) {
    case class T(src: Chars) extends Token { val category: Str.type = Str }

    override val hashCode = kind_name.hashCode
    def similarity(t1: Str.T, t2: Str.T, approx: Boolean = false): Double =
      Math.max(Score.related, t1.src.compare(t2.src, approx = approx))
  }

  object Term_Var { case class T(src: Chars, typing: List[String], category: Term_Var) extends Token }
  case class Term_Var(typing: Set[String]) extends Category(Kind.term_var) {
    override val hashCode = (kind_name, typing).hashCode

    def similarity(t1: Term_Var.T, t2: Term_Var.T, approx: Boolean = false): Double =
      if (t1.typing == t2.typing) Math.max(Score.similar, t1.src.compare(t2.src))
      else Math.min(Score.mostly, Math.max(Score.related, t1.src.compare(t2.src)))
  }

  object Typ_Var { case class T(src: Chars, sorting: List[String], category: Typ_Var) extends Token }
  case class Typ_Var(sorting: Set[String]) extends Category(Kind.typ_var) {
    override val hashCode = (kind_name, sorting).hashCode

    def similarity(t1: Typ_Var.T, t2: Typ_Var.T, approx: Boolean = false): Double =
      if (t1.sorting == t2.sorting) Math.max(Score.similar, t1.src.compare(t2.src))
      else Math.min(Score.mostly, Math.max(Score.related, t1.src.compare(t2.src)))
  }

  object Inner { case class T(category: Inner) extends Token }
  case class Inner(rep: String) extends Category(Kind.inner) {
    override val hashCode = (kind_name, rep).hashCode
  }

  object Entity { case class T(name: String, category: Entity) extends Token }
  case class Entity(base_name: String, kind: String) extends Category(Kind.entity) {
    override val hashCode = (base_name, kind_name, kind).hashCode
    def similarity(t1: Entity.T, t2: Entity.T): Double =
      if (t1.name == t2.name) Score.same else Score.mostly
  }

  case object Proof extends Category(Kind.proof) {
    case class T(src: Chars) extends Token { val category: Proof.type = Proof }

    override val hashCode = kind_name.hashCode
    def similarity(t1: T, t2: T, approx: Boolean = false): Double = {
      val l1 = t1.src.length.toDouble
      val l2 = t2.src.length.toDouble
      Math.max(Score.similar,
        Math.max(Math.min(Score.mostly, Math.min(l1 / l2, l2 / l1)),
          t1.src.compare(t2.src, approx = approx)))
    }
  }

  object Unknown { case class T(src: Chars, category: Unknown) extends Token }
  case class Unknown(kind: String) extends Category(Kind.unknown) {
    override val hashCode = (kind_name, kind).hashCode
    def similarity(t1: Unknown.T, t2: Unknown.T, approx: Boolean = false): Double =
      Math.max(Score.similar, t1.src.compare(t2.src, approx = approx))
  }

  case object Delete extends Category(Kind.delete) with Token { val category: Delete.type = this }


  /* token spans */

  object Span {
    private val sep: Byte = 30

    def store(spans: List[Span], file: Path): Unit = {
      Isabelle_System.make_directory(file.dir)
      Bytes.write(file, Bytes.empty)

      val cache = Compress.Cache.make()
      val options_zstd = Compress.Options_Zstd()
      def make_stream: zstd.ZstdOutputStream =
        new zstd.ZstdOutputStream(
          new BufferedOutputStream(
            new FileOutputStream(file.file)), cache.for_zstd, options_zstd.level)

      using(make_stream) { out =>
        for (span <- spans) {
          YXML.bytes_of_body(Encode.span(span)).write_stream(out)
          out.write(sep)
        }
      }
    }

    def load(file: Path): List[Span] = {
      val options_zstd = Compress.Options_Zstd()
      val compress_cache = Compress.Cache.make()

      def make_stream =
        new zstd.ZstdInputStream(
          new BufferedInputStream(new FileInputStream(file.file)), compress_cache.for_zstd)

      using(make_stream) { in =>
        val chunks =
          new Iterator[Bytes] {
            val buf = new Array[Byte](Bytes.block_size)
            var m = in.read(buf)
            var n = 0
  
            override def hasNext: Boolean = n < m
            override def next(): Bytes = {
              var res = Bytes.empty
              val n0 = n
              while (n < m && !buf.drop(n).contains(sep)) {
                res = res + Bytes(buf.drop(n))
                m = in.read(buf)
                n = 0
              }
              if (n < m) {
                val l = buf.drop(n).indexOf(sep)
                res = res + Bytes(buf.slice(n, n + l))
                n = n + l + 1
                if (n == m) {
                  m = in.read(buf)
                  n = 0
                }
              }
              res
            }
          }

        val cache = Cache.make(compress = compress_cache)
        (for (chunk <- chunks) yield Decode.span(YXML.parse_body(chunk)).cache(cache)).toList
      }
    }
  }

  class Span private[Clone_Detect](
    val id: Int,
    val tokens: List[Token],
    val node: Document.Node.Name,
    val range: Text.Range,
    val kinds: Set[String],
    val src: String,
    val terms: List[Term.Term]
  ) {
    val token_length = tokens.length

    override val hashCode: Int = id
    override def equals(that: Any): Boolean =
      that match {
        case other: Span => other.id == id
        case _ => false
      }
    override def toString: String =
      node.toString + range + ":\n" + Library.indent_lines(2, src) + "\n"

    val categories: List[Category] = tokens.map(_.category).distinct
    val categorized: Map[Category, List[Token]] =
      tokens.groupMapReduce(_.category)(List(_))(_ ++ _)
    def relevance_accum(tokens: List[Token]): Vector[Double] = {
      var total = 0.0
      0.0 +:
        (for (v <- tokens.map(_.category.relevance).sorted.reverse) yield {
          total = total + v
          total
        }).toVector
    }
    val categorized_relevance_accum: Map[Category, Vector[Double]] =
      categorized.map((category, tokens) => category -> relevance_accum(tokens))
    val token_relevance_accum: Vector[Double] = relevance_accum(tokens)
    val relevance: Double = token_relevance_accum.last
    lazy val hnf_terms = terms.map(HNF_Term.build)
    def cache(cache: Cache): Span =
      new Span(id, tokens.map(cache.token), node, range, kinds, src, terms.map(cache.term))
  }

  /** cache **/

  object Cache {
    def make(
      compress: Compress.Cache = Compress.Cache.make(),
      max_string: Int = isabelle.Cache.default_max_string,
      initial_size: Int = isabelle.Cache.default_initial_size
    ): Cache = new Cache(compress, initial_size, max_string)

    val none: Cache = make(max_string = 0)
  }

  class Cache(compress: Compress.Cache, max_string: Int, initial_size: Int)
    extends Term.Cache(compress, max_string, initial_size) {
    protected def cache_chars(x: Chars): Chars = lookup(x) getOrElse store(Chars(cache_string(x.s)))

    protected def cache[A](x: A): A = lookup(x) getOrElse store(x)

    protected def cache_token(x: Token): Token =
      lookup(x) match {
        case Some(y) => y
        case None =>
          x match {
            case Command.T(name, category) => store(Command.T(cache_string(name), cache(category)))
            case Keyword.T(category) => store(Keyword.T(cache(category)))
            case Comment.T(src) => store(Comment.T(cache_chars(src)))
            case Str.T(src) => store(Str.T(cache_chars(src)))
            case Term_Var.T(src, typing, category) =>
              store(Term_Var.T(cache_chars(src), typing.map(cache_string), cache(category)))
            case Typ_Var.T(src, sorting, category) =>
              store(Typ_Var.T(cache_chars(src), sorting.map(cache_string), cache(category)))
            case Inner.T(category) => store(Inner.T(cache(category)))
            case Entity.T(name, category) => store(Entity.T(cache_string(name), cache(category)))
            case Proof.T(src) => store(Proof.T(cache_chars(src)))
            case Unknown.T(src, category) => store(Unknown.T(cache_chars(src), cache(category)))
            case Delete => Delete
          }
      }

    def token(x: Token): Token = if (no_cache) x else synchronized { cache_token(x) }
  }


  /* index */

  object Index {
    def apply(
      spans: List[Span],
      min_length: Int = 10,
      threshold: Double = 0.9,
      progress: Progress = new Progress
    ): Index = {
      def filter(span: Span): Boolean =
        span.kinds.nonEmpty && span.tokens.length >= min_length

      val spans1 = spans.filter(filter)

      val stats = Stats.build(spans1)
      if (progress.verbose) progress.echo(stats.print(), verbose = true)

      val prepared =
        for ((kinds, spans) <- spans1.groupMapReduce(_.kinds)(List(_))(_ ::: _)) yield kinds -> {
          val stats = Stats.build(spans)
          def minimal_categories(span: Span): List[Category] =
            span.categorized.toList
              .map((category, tokens) => category -> tokens.length)
              .sortBy((category, _) => stats.category(category))
              .foldRight((List.empty[Category], threshold * span.relevance)) {
                case ((category, count), (acc, removable)) =>
                    val relevance = category.relevance * count.toDouble
                    if (relevance >= removable) (category :: acc, removable)
                    else (acc, removable - relevance)
              }._1

          val categorized =
            (for {
              span <- spans
              category <- minimal_categories(span)
            } yield category -> span).groupMapReduce(_._1)((_, span) => List(span))(_ ::: _)
          for ((category, spans) <- categorized) yield category -> spans.sortBy(_.id)
        }

      new Index(spans1, stats, threshold, prepared, progress)
    }
  }

  object Stats {
    def build(spans: List[Span]): Stats = {
      val tokens = spans.flatMap(_.tokens)
      val token_stats = tokens.groupMapReduce(identity)(_ => 1)(_ + _)
      val category_stats =
        (for {
          span <- spans
          category <- span.categories
        } yield category -> span).groupMapReduce(_._1)(_ => 1)(_ + _)
      val names = tokens.collect { case Entity.T(name, _) => name }
      val name_stats = names.map(base).groupMapReduce(identity)(_ => 1)(_ + _)
      Stats(token_stats, category_stats, name_stats)
    }
  }

  case class Stats(token: Map[Token, Int], category: Map[Category, Int], name: Map[String, Int]) {
    def print(num: Int = 10): String = {
      def print_token(t: (Token, Int)): String = t._1.toString + ": " + t._2 + "\n"
      def print_category(t: (Category, Int)): String = t._1.toString + ": " + t._2 + "\n"
      def print_name(t: (String, Int)): String = t._1 + ": " + t._2 + "\n"

      val tokens = token.toList.sortBy(_._2).reverse.take(num).map(print_token).mkString
      val categories = category.toList.sortBy(_._2).reverse.take(num).map(print_category).mkString
      val names = name.toList.sortBy(_._2).reverse.take(num).map(print_name).mkString

      List(
        "Tokens:", Library.indent_lines(2, tokens),
        "Categories:", Library.indent_lines(2, categories),
        "Names:", Library.indent_lines(2, names)).mkString("\n")
    }
  }

  class Index private(
    val spans: List[Span],
    val stats: Stats,
    val threshold: Double,
    prepared: Map[Set[String], Map[Category, List[Span]]],
    progress: Progress
  ) {
    val size: Int = spans.length

    def retrieve(span1: Span): Iterator[Span] = {
      val max = span1.id

      def merge(l1: List[Span], l2: List[Span]): List[Span] =
        l2 match {
          case Nil => l1
          case x :: xs =>
            if (x.id >= max) l1
            else l1 match {
              case Nil => x :: merge(Nil, xs)
              case y :: ys =>
                if (y.id < x.id) y :: merge(ys, l2)
                else if (x.id < y.id) x :: merge (l1, xs)
                else x :: merge(ys, xs)
            }
        }

      val spans = prepared.getOrElse(span1.kinds, Map.empty)
      span1.categories.foldLeft(List.empty[Span])(
        { case (res, category) => merge(res, spans.getOrElse(category, Nil)) }).iterator
    }

    def clones: List[Clone_Class] = {
      progress.echo("Finding clones for " + spans.length + " spans ...", verbose = true)

      class Stats {
        var retrieved = 0L
        var size_match_uncategorized = 0L
        var different_thy = 0L
        var size_match = 0L
        var approx_relaxed_match = 0L
        def +(other: Stats): Stats = {
          retrieved = retrieved + other.retrieved
          size_match_uncategorized = size_match_uncategorized + other.size_match_uncategorized
          different_thy = different_thy + other.different_thy
          size_match = size_match + other.size_match
          approx_relaxed_match = approx_relaxed_match + other.approx_relaxed_match
          this
        }
      }

      def token_candidates(span1: Span): (List[Matching], Stats) = {
        val stats = new Stats
        val res =
          (for {
            span2 <- retrieve(span1)
            _ = stats.retrieved = stats.retrieved + 1
            if Matching.size_score(span1, span2, uncategorized = true) > threshold
            _ = stats.size_match_uncategorized = stats.size_match_uncategorized + 1
            if Matching.size_score(span1, span2) > threshold
            _ = stats.size_match = stats.size_match + 1
            if Matching(span1, span2, approx = true, relaxed = true).score > threshold
            _ = stats.approx_relaxed_match = stats.approx_relaxed_match + 1
            matching = Matching(span1, span2)
            if matching.score > threshold
          } yield matching).toList
        (res, stats)
      }

      def num_pairs(n: Long): Long = n * (n-1L) / 2L
      val potential =
        prepared.toList.map((_, cats) =>
          num_pairs(cats.toList.flatMap(_._2).distinct.length.toLong)).sum
      progress.echo("Potential: " + potential)

      val start = Time.now()
      val (candidatess, statss) = Par_List.map(token_candidates, spans).unzip
      val (candidates, stats) = (candidatess.flatten, statss.foldLeft(new Stats)(_ + _))
      val timing = Time.now() - start

      progress.echo("Found " + candidates.length + " token matches in " + timing.message + ":\n" +
        "  Retrieved: " + stats.retrieved + "\n" +
        "  Matching size (uncategorized): " + stats.size_match_uncategorized + "\n" +
        "  Matching size: " + stats.size_match + "\n" +
        "  Matching (approximate and relaxed): " + stats.approx_relaxed_match, verbose = true)

      class Term_Stats {
        var size_match = 0L
        var matching = 0L
        def +(other: Term_Stats): Term_Stats = {
          size_match = size_match + other.size_match
          matching = matching + other.matching
          this
        }
      }

      def term_candidates(matching: List[Matching]): (List[Matching], Term_Stats) = {
        def candidate(matching: Matching): (Option[Matching], Term_Stats) = {
          val stats = new Term_Stats()
          val res =
            for {
              matching <- Option(matching)
              if matching.by_terms(size_score = true).score > threshold
              _ = stats.size_match = stats.size_match + 1
              matching1 = matching.by_terms()
              if matching1.score > threshold
              _ = stats.matching = stats.matching + 1
              if matching1.left.node != matching1.right.node
            } yield matching1
          (res, stats)
        }

        val (matchingss, statss) = Par_List.map(candidate, matching).unzip
        (matchingss.flatten, statss.foldLeft(new Term_Stats())(_ + _))
      }

      val start1 = Time.now()
      val (matchings, term_stats) = term_candidates(candidates)
      val timing1 = Time.now() - start1

      if (term_stats.matching != candidates.length) {
        progress.echo("Found " + matchings.length + " term matches in " + timing1.message + ":\n" +
          "  Matching size: " + term_stats.size_match + "\n" +
          "  Matching: " + term_stats.matching, verbose = true)
      }
      progress.echo("  In different theories: " + matchings.size + "\n", verbose = true)

      Clone_Class.make(matchings).sortBy(cls => (cls.max_score, cls.min_score)).reverse
    }
  }


  /* token spans from markup */

  val command_blacklisted: Set[String] = Set("termination", "instance", "instantiation")

  val keywords =
    Markup.Elements(Markup.KEYWORD, Markup.KEYWORD1, Markup.KEYWORD2, Markup.KEYWORD3,
      Markup.QUASI_KEYWORD, Markup.OPERATOR, Markup.LOAD_COMMAND)
  val comments = Markup.Elements(Markup.COMMENT, Markup.COMMENT1, Markup.COMMENT2, Markup.COMMENT3)
  val strings = Markup.Elements(Markup.STRING, Markup.ALT_STRING, Markup.CARTOUCHE, Markup.IMPROPER)
  val term_var = Markup.Elements(Markup.FREE, Markup.SKOLEM, Markup.BOUND, Markup.VAR)
  val typ_var = Markup.Elements(Markup.TFREE, Markup.TVAR)
  val inner =
    Markup.Elements(Markup.NUMERAL, Markup.DELIMITER, Markup.INNER_STRING, Markup.INNER_CARTOUCHE)
  val entity = Markup.Elements(Markup.ENTITY)
  val delete = Markup.Elements(Markup.DELETE)

  def expand_block(block: Thy_Blocks.Block): List[Thy_Blocks.Block] =
    if (command_blacklisted(block.command)) Nil
    else {
      block match {
        case Thy_Blocks.Thy(inner) => inner.flatMap(expand_block)
        case e@Thy_Blocks.Decl(inner) =>
          val inner1 = inner.flatMap(expand_block)
          if (inner.length > 1) inner1 else List(e)
        case _ => List(block)
      }
    }

  @tailrec def read_sorting(body: XML.Body): Option[List[String]] =
    body match {
      case List(XML.Wrapped_Elem(Markup(Markup.SORTING, _), body, _)) =>
        Some(Markup_Tree.from_XML(body).cumulate(
          Text.Range.full,
          List.empty[String],
          entity,
          { 
            case (_, Text.Info(_, XML.Elem(Markup.Entity(Markup.CLASS, name), _))) =>
              Some(List(name))
            case _ => error("Invalid sorting")
          }).flatMap(_.info).sorted)
      case List(XML.Elem(_, body)) => read_sorting(body)
      case _ => None
    }

  @tailrec def read_typing(body: XML.Body): Option[List[String]] =
    body match {
      case List(XML.Wrapped_Elem(Markup(Markup.TYPING, _), body, _)) =>
        Some(Markup_Tree.from_XML(body).cumulate(
          Text.Range.full,
          List.empty[String],
          entity,
          {
            case (_, Text.Info(_, XML.Elem(Markup.Entity(Markup.TYPE_NAME, name), _))) =>
              Some(List(name))
            case (_, Text.Info(_, XML.Elem(Markup.Entity(Markup.CLASS, name), _))) =>
              Some(List(name))
            case (_, Text.Info(_, elem)) => error("Invalid typing element: " + elem)
          }).flatMap(_.info).sorted)
      case List(XML.Elem(_, body)) => read_typing(body)
      case _ => None
    }

  def read_spans(
    counter: Counter,
    snapshot: Snapshot,
    theory: Export_Theory.Theory,
    cache: Cache = Cache.make()
  ): List[Span] = {
    val markup = snapshot.xml_markup()
    val markup_tree = Markup_Tree.from_XML(markup)
    val content = XML.content(markup)
    def get_src(range: Text.Range): String =
      Symbol.decode(Line.normalize(range.substring(content))).trim

    val index = Symbol.Index(content)

    val spans0 =
      for (block0 <- Thy_Blocks.read_blocks(snapshot).flatMap(expand_block)) yield {
        val (block, tokens0) =
          block0 match {
            case Thy_Blocks.Prf(hd :: rest) =>
              (hd, List(Proof.T(Chars(rest.map(_.range).map(get_src).mkString))))
            case _ => (block0, Nil)
          }

        def in_block(entity: Export_Theory.Entity[_]): Boolean =
          entity.file == snapshot.node_name.node && block.range.contains(index.decode(entity.range))

        val kinds =
          (for (entity <- theory.entity_iterator if in_block(entity)) yield entity.kind).toSet

        val thms =
          for {
            thm <- theory.thms
            if in_block(thm)
            content <- thm.content
          } yield content.prop.term

        val tokens = 
          block.spans.flatMap { span =>
            def token(range: Text.Range, name: String, props: Properties.T): Token = {
              val src = get_src(range)

              if (strings(name)) Str.T(Chars(src))
              else if (comments(name)) Comment.T(Chars(src))
              else if (keywords(name)) {
                props match {
                  case Markup.Kind(kind) if kind == Markup.COMMAND =>
                    Command.T(span.command, Command(span.kind))
                  case _ if name == Markup.LOAD_COMMAND =>
                    Command.T(span.command, Command(span.kind))
                  case _ => Keyword.T(Keyword(src))
                }
              }
              else if (inner(name)) Inner.T(Inner(src))
              else if (typ_var(name)) {
                read_sorting(snapshot.xml_markup(range)) match {
                  case Some(sorting) => Typ_Var.T(Chars(src), sorting, Typ_Var(sorting.toSet))
                  case None => Str.T(Chars(src))
                }
              }
              else if (term_var(name)) {
                read_typing(snapshot.xml_markup(range)) match {
                  case Some(typing) => Term_Var.T(Chars(src), typing, Term_Var(typing.toSet))
                  case None => Str.T(Chars(src))
                }
              }
              else if (entity(name)) {
                val kind = Markup.Kind.unapply(props).getOrElse("")
                val name = Markup.Name.unapply(props).getOrElse(src)

                Entity.T(name, Entity(base(name), kind))
              }
              else if (delete(name)) Delete
              else Unknown.T(Chars(src), Unknown(name))
            }

            val token_infos = 
              markup_tree.cumulate[Text.Info[Token]](
                span.range,
                Text.Info(span.range, Unknown.T(Chars(get_src(span.range)), Unknown(""))),
                Markup.Elements.full,
                {
                  case (
                    Text.Info(range0, token0),
                    Text.Info(range1, XML.Elem(Markup(name, props), _))) =>
                    val token1 = token(range1, name, props)

                    val more_specific =
                      Category.specifity.lt(token0.category, token1.category) ||
                        (Category.specifity.lteq(token0.category, token1.category) &&
                          range0 != range1)
                    if (more_specific) Some(Text.Info(range1, token1)) else None
                })

            token_infos.flatMap {
              case Text.Info(range0, Text.Info(range1, token)) =>
                val src = get_src(range0)
                if (Symbol.all_blank(src) || token == Delete) None
                else if (range0 == range1) Some(token)
                else {
                  token match {
                    case Delete => None
                    case t: Comment.T => Some(t.copy(src = Chars(get_src(range0))))
                    case t: Str.T => Some(t.copy(src = Chars(get_src(range0))))
                    case t: Inner.T => Some(t.copy(category = Inner(get_src(range0))))
                    case t: Unknown.T => Some(t.copy(src = Chars(get_src(range0))))
                    case _ => Some(token)
                  }
                }
            }
          }
        (tokens ::: tokens0, snapshot.node_name, block0.range, kinds, get_src(block0.range), thms)
      }
    for ((tokens, node, range, kinds, src, thms) <- spans0)
    yield new Span(counter().toInt, tokens.map(cache.token), node, range, kinds, src, thms)
  }


  /* encode/decode */

  object Encode {
    import XML.Encode.*
    import Term_XML.Encode.*

    val token: T[Token] = {
      def named(pf: PartialFunction[Token, XML.Body]): V[Token] =
        { case token if pf.isDefinedAt(token) => (List(token.category.kind_name), pf(token)) }
      variant(List(
        named { case Command.T(name, Command(kind)) => pair(string, string)(name, kind) },
        named { case Keyword.T(Keyword(rep)) => string(rep) },
        named { case Comment.T(Chars(s)) => string(s) },
        named { case Str.T(Chars(s)) => string(s) },
        named { case Term_Var.T(Chars(name), typing1, Term_Var(typing2)) => triple(string, list(string), list(string))(name, typing1, typing2.toList) },
        named { case Typ_Var.T(Chars(name), sorting1, Typ_Var(sorting2)) => triple(string, list(string), list(string))(name, sorting1, sorting2.toList) },
        named { case Inner.T(Inner(rep)) => string(rep) },
        named { case Proof.T(Chars(s)) => string(s) },
        named { case Entity.T(name, Entity(base_name, kind)) => triple(string, string, string)(name, base_name, kind) },
        named { case Unknown.T(Chars(s), Unknown(kind)) => pair(string, string)(s, kind) }))
    }

    val span: T[Span] =
      { (span: Span) =>
        pair(int,
          pair(list(token),
            pair(pair(string, string),
              pair(pair(int, int),
                pair(list(string),
                  pair(string, list(term)))))))(
          (span.id,
            (span.tokens,
              ((span.node.node, span.node.theory),
                ((span.range.start, span.range.stop),
                  (span.kinds.toList,
                    (span.src, span.terms)))))))
      }
  }

  object Decode {
    import XML.Decode.*
    import Term_XML.Decode.*

    val token: T[Token] = {
      def named(kind: Kind)(f: XML.Body => Token): V[Token] =
        { case (List(s), body) if kind.toString == s => f(body) }
      variant(List(
        named(Kind.command) { body => val (a, b) = pair(string, string)(body); Command.T(a, Command(b)) },
        named(Kind.keyword) { body => Keyword.T(Keyword(string(body))) },
        named(Kind.comment) { body => Comment.T(Chars(string(body))) },
        named(Kind.str) { body => Str.T(Chars(string(body))) },
        named(Kind.term_var) { body => val (a, b, c) = triple(string, list(string), list(string))(body); Term_Var.T(Chars(a), b, Term_Var(c.toSet)) },
        named(Kind.typ_var) { body => val (a, b, c) = triple(string, list(string), list(string))(body); Typ_Var.T(Chars(a), b, Typ_Var(c.toSet)) },
        named(Kind.inner) { body => Inner.T(Inner(string(body))) },
        named(Kind.proof) { body => Proof.T(Chars(string(body))) },
        named(Kind.entity) { body => val (a, b, c) = triple(string, string, string)(body); Entity.T(a, Entity(b, c)) },
        named(Kind.unknown) { body => val (a, b) = pair(string, string)(body); Unknown.T(Chars(a), Unknown(b)) }))
    }

    val span: T[Span] =
      { (body: XML.Body) =>
        val (a, (b, ((c, d), ((e, f), (g, (h, i)))))) =
          pair(int,
            pair(list(token),
              pair(pair(string, string),
                pair(pair(int, int),
                  pair(list(string),
                    pair(string, list(term)))))))(body)
        new Span(a, b, Document.Node.Name(c, d), Text.Range(e, f), g.toSet, h, i)
      }
  }


  /* clone detection */

  def clone_detect(
    options: Options,
    threshold: Double,
    progress: Progress = new Progress,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    read_file: Option[Path] = None,
    write_file: Option[Path] = None,
    selection: Sessions.Selection = Sessions.Selection.empty,
  ): Unit = {
    val cache = Cache.make()
    val spans =
      read_file match {
        case None =>
          val store = Store(options)
          val counter = Counter.make()

          val full_sessions =
            Sessions.load_structure(options = options, dirs = dirs, select_dirs = select_dirs)

          val sessions_structure = full_sessions.selection(selection)
          val deps = Sessions.Deps.load(sessions_structure)

          def timing_msg[A](phase: String)(res: Exn.Result[A]): String =
            res match { case Exn.Res(res) => phase + " took" case _ => null }

          val sessions = sessions_structure.build_topological_order

          val spans = 
            Timing.timeit(
              sessions.filterNot(Sessions.is_pure).flatMap { session_name =>
                using(Export.open_session_context0(store, session_name))(session_context => {
                  deps(session_name).proper_session_theories.flatMap { name =>
                    val thy = name.theory
                    val thy_heading = "\nTheory " + quote(thy) + ":"

                    progress.echo("Theory " + quote(thy) + " ...", verbose = true)

                    val theory_context = session_context.theory(thy)

                    Build.read_theory(theory_context) match {
                      case None =>
                        progress.echo_warning(thy_heading + " missing")
                        Nil
                      case Some(snapshot) =>
                        read_spans(
                          counter, snapshot, Export_Theory.read_theory(theory_context), cache)
                    }
                  }
                })
              },
              timing_msg("indexing"))

          if (progress.verbose) {
            val unknown = spans
              .flatMap(_.tokens).map(_.category)
              .collect({ case Unknown(kind) => kind }).distinct
            progress.echo("Unknown markup: " + commas_quote(unknown), verbose = true)
          }

          write_file.foreach(Span.store(spans, _))
          spans

        case Some(file) =>
          progress.echo("Reading spans from " + file.implode)
          Span.load(file)
      }

    val index = Index(spans, threshold = threshold, progress = progress)

    val result = index.clones
    val max = 100
    progress.echo(result.take(max).reverse.mkString("\n\n\n"))
    progress.echo(
      (if (result.length > max) max.toString + "/" else "") + result.length + " clone classes shown")
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("clone_detect", "detect clones in Isabelle theories", Scala_Project.here,
    { args =>
      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var read_file: Option[Path] = None
      var write_file: Option[Path] = None
      var requirements = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var dirs: List[Path] = Nil
      var session_groups: List[String] = Nil
      var no_build = false
      var options = Options.init()
      var threshold = 0.9
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle clone_detect [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -I FILE      read index file directly
    -O FILE      write index file
    -R           refer to requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -d DIR       include session directory
    -g NAME      select session group NAME
    -n           no build
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -t NUMBER    threshold for detection in [0, 1] (default: """ + threshold + """)
    -v           verbose mode
    -x NAME      exclude session NAME and all descendants

  Detects clones in the given sessions.

""",
        "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
        "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
        "I:" -> (arg => read_file = Some(Path.explode(arg))),
        "O:" -> (arg => write_file = Some(Path.explode(arg))),
        "R" -> (_ => requirements = true),
        "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
        "a" -> (_ => all_sessions = true),
        "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
        "g:" -> (arg => session_groups = session_groups ::: List(arg)),
        "n" -> (_ => no_build = true),
        "o:" -> (arg => options = options + arg),
        "t:" -> (arg => threshold = Value.Double.parse(arg)),
        "v" -> (_ => verbose = true),
        "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)
      if (read_file.isDefined && write_file.isDefined) getopts.usage()

      val progress = new Console_Progress(verbose = verbose)

      val selection = Sessions.Selection(
        requirements = requirements,
        all_sessions = all_sessions,
        base_sessions = base_sessions,
        exclude_session_groups = exclude_session_groups,
        exclude_sessions = exclude_sessions,
        session_groups = session_groups,
        sessions = sessions)

      if (!no_build && read_file.isEmpty) {
        progress.interrupt_handler {
          val res = Build.build(
            options + "export_theory", selection = selection, progress = progress,
            dirs = dirs, select_dirs = select_dirs, build_heap = true)
          if (!res.ok) System.exit(res.rc)
        }
      }

      clone_detect(options, threshold, progress = progress, dirs = dirs, select_dirs = select_dirs,
        read_file = read_file, write_file = write_file, selection = selection)
    })
}

class Clone_Detect_Tool extends Isabelle_Scala_Tools(Clone_Detect.isabelle_tool)
