(* TODO relocate to Table.ML *)
structure Intreltab = Table(type key = int * int
  val ord = prod_ord int_ord int_ord);

signature RELOCATE_DEPS =
sig
  type entry =
    {concealed: bool,
     group: serial,
     pos: Position.T,
     serial: serial,
     suppress: bool list,
     theory_long_name: string,
     name: string,
     kind: string}
  val eq_entry: entry * entry -> bool
  val pretty_entry: entry -> Pretty.T
  val pretty_thy: theory -> Pretty.T
  type dep = {serial: serial, n: int}
  val eq_dep: dep * dep -> bool
  type 'a deps
  val join: (serial -> 'a -> 'b -> 'c) -> 'a deps -> 'b deps -> 'c deps
  val map_dep: (serial -> 'a -> 'b) -> 'a deps -> 'b deps
  val map_deps: (dep -> 'a) -> int deps -> 'a deps
  val dest_deps: int deps -> dep list
  val dest: 'a deps -> (serial * 'a) list
  type node = int deps * entry * int deps
  val node_serial: node -> serial
  val eq_node: node * node -> bool
  val build: theory -> Proof.context -> thm list ->
    int deps * node Inttab.table * (node list Inttab.table * (int * node list) list) Symtab.table
  val lookup_thm_pos: Proof.context -> 
    (node list Inttab.table * (int * node list) list) Symtab.table -> thm ->
    (node list Inttab.table * (int * node list)) option
end

structure Relocate_Deps: RELOCATE_DEPS =
struct
type entry =
  {concealed: bool,
   group: serial,
   pos: Position.T,
   serial: serial,
   suppress: bool list,
   theory_long_name: string,
   name: string,
   kind: string}
val eq_entry = op = o apply2 #serial
fun mk_entry {concealed: bool, group: serial, pos: Position.T, serial: serial, suppress: bool list,
 theory_long_name: string} name space = 
  {concealed=concealed, group=group, pos=pos, serial=serial, suppress=suppress,
   theory_long_name=theory_long_name, name=name, kind=Name_Space.kind_of space}


(* Position ordering by line (in interactive mode, find via PIDE) *)

fun pos_line pos = case Position.line_of pos of SOME line => line | NONE =>
  case (Position.id_of pos, Position.offset_of pos) of
    (SOME id, SOME offset) =>
      (Value.parse_int o the_single) (\<^scala>\<open>source_line\<close> [id, string_of_int offset])
  | _ => error "No line"
val pos_ord = int_ord o apply2 pos_line


(* Pretty printing *)

fun pretty_entry {serial, pos, name, kind, ...} =
  Pretty.mark_str (Position.make_entity_markup {def = false} serial kind (name, pos), name)

fun pretty_thy theory =
  Pretty.mark_str (Theory.get_markup theory, Context.theory_long_name theory)


(* Pure namespace *)

fun space_serials space = Name_Space.get_names space |> map (#serial o Name_Space.the_entry space)

val pure_space =
  let
    val thy = @{theory Pure}
    val ctxt = Proof_Context.init_global thy
    val cls_space = Sign.class_space thy
    val typ_space = Sign.type_space thy
    val const_space = Sign.const_space thy
    val thm_space = (Facts.space_of o Proof_Context.facts_of) ctxt
  in
    [cls_space, typ_space, const_space, thm_space]
    |> maps space_serials |> map (rpair ()) |> Inttab.make
  end

val exclude = ["HOL.Quickcheck_Narrowing", "HOL.Code_Numeral"]

fun excluded {theory_long_name, serial, ...} =
  Inttab.defined pure_space serial orelse member (op =) exclude theory_long_name  


(* imports graph width edges to parent: \<succ> *)

fun build_imports thy =
  let
    fun build_edges thy graph =
      let val name = Context.theory_long_name thy
      in
        if String_Graph.defined graph name then graph else
          let val parents = Theory.parents_of thy
          in
            graph
            |> (String_Graph.new_node (name, thy))
            |> fold build_edges parents
            |> fold (fn dep =>
                String_Graph.add_edge (name, dep)) (map Context.theory_long_name parents)
          end
      end
  in build_edges thy String_Graph.empty end


(* dependencies: \<D>(i) *)

fun build_deps thy ctxt imports thms =
  let
    val facts = Proof_Context.facts_of ctxt

    val cls_space = Sign.class_space thy
    val typ_space = Sign.type_space thy
    val const_space = Sign.const_space thy
    val thm_space = Facts.space_of facts

    val thm_serial = #serial o (Name_Space.the_entry thm_space o fst o Thm.get_name_hint)

    val thms_deps = Thm_Deps.thm_deps thy thms |> map (fst o snd)
    val thms_terms = map Thm.prop_of thms
    val thms_serials = map thm_serial thms

    fun collect_sort f = fold (f cls_space)
    fun collect_typ f (Type (name, typs)) tab = fold (collect_typ f) typs (f typ_space name tab)
      | collect_typ f (TFree (_, sort)) tab = collect_sort f sort tab
      | collect_typ f (TVar (_, sort)) tab = collect_sort f sort tab
    fun collect_term f (Const (name, typ)) tab = (f const_space name (collect_typ f typ tab))
      | collect_term f (Free (_, typ)) tab = collect_typ f typ tab
      | collect_term f (Var (_, typ)) tab = collect_typ f typ tab
      | collect_term _ (Bound _) tab = tab
      | collect_term f (Abs (_, typ, term)) tab = collect_typ f typ (collect_term f term tab)
      | collect_term f (term1 $ term2) tab = collect_term f term1 (collect_term f term2 tab)

    fun upd_inttab space name =
      let
        val elem = Name_Space.the_entry space name
        val serial = #serial elem
        val entry = mk_entry elem name space
        val skip = excluded entry orelse member (op =) thms_serials serial
      in if skip then I else Inttab.update (serial, entry) end

    fun by_thy entries =
      (entries
        |> map (fn (_, entry) => (#theory_long_name entry, entry))
        |> fold (fn (thy_name, entry) =>
          Symtab.map_default (thy_name, [entry]) (fn entries => entry::entries))) Symtab.empty

    fun trans_imports dir thys =
      imports
      |> String_Graph.restrict (member (op =) (fold (union (op =) o dir imports o single) thys []))

    val thys_deps = 
      Inttab.empty
      |> (fold (collect_term upd_inttab) thms_terms)
      |> (fold (upd_inttab thm_space) thms_deps)
      |> fold Inttab.delete_safe thms_serials
      |> Inttab.dest
      |> by_thy 

    fun first_entry f = hd o sort (f o pos_ord o apply2 #pos)

    (* find lower bound where thm may be placed: \<P>(i) lhs; rhs needs graph first*)
    val lower_thys =
      (trans_imports String_Graph.all_succs (Symtab.keys thys_deps)
      |> String_Graph.minimals
      |> fold (inter (op =) o String_Graph.all_preds imports o single)) (String_Graph.keys imports)
    val lower_bound =
      lower_thys
      |> map (swap o ` (Option.map (first_entry rev_order) o Symtab.lookup thys_deps))
      |> Symtab.make

    val pretty_thy = pretty_thy o String_Graph.get_node imports
    val _ =
      if Context_Position.is_visible ctxt then
        Pretty.writeln_chunks
          (case
            imports |> String_Graph.restrict (Symtab.defined lower_bound) |> String_Graph.maximals 
           of
            [single] => 
              [Pretty.block
                (case the (Symtab.lookup lower_bound single) of
                  NONE => [Pretty.str "May be placed in ", pretty_thy single]
                | SOME entry => [Pretty.str "May be placed after ", pretty_entry entry])]
          | xs =>
              (Pretty.str "May be placed in any of:") :: 
                (xs |> map (Pretty.item o single o pretty_thy)))
        else ()

    fun add_thms (name, thms) (graph, mult) =
      let
        val (elem as {theory_long_name, serial, ...}) = Name_Space.the_entry thm_space name
        val entry = mk_entry elem name thm_space
        val include_thm = not (excluded entry) andalso Symtab.defined lower_bound theory_long_name

        fun add_dep space name (graph, mult) =
          let
            val (elem as {serial = serial1, ...}) = Name_Space.the_entry space name
            val entry = mk_entry elem name space
          in if excluded entry then (graph, mult) else
            (graph
              |> (if Int_Graph.defined graph serial1 then I else Int_Graph.new_node (serial1, entry))
              |> Int_Graph.add_edge (serial, serial1),
             Intreltab.map_default ((serial, serial1), 1) (curry (op +) 1) mult)
          end
      in 
        if not include_thm then (graph, mult) else
          (if Int_Graph.defined graph serial then (graph, mult) 
           else (Int_Graph.new_node (serial, entry) graph, mult))
          |> fold (add_dep thm_space) (Thm_Deps.thm_deps thy thms |> map (fst o snd))
          |> fold (collect_term add_dep) (map Thm.prop_of thms)
      end

    val (graph, mult) = Facts.fold_static add_thms facts (Int_Graph.empty, Intreltab.empty)

    val thys_depd =
      Int_Graph.all_preds graph thms_serials
      |> subtract (op =) thms_serials
      |> map (swap o ` (Int_Graph.get_node graph))
      |> by_thy

    val all_upper = trans_imports String_Graph.all_preds (Symtab.keys thys_depd)
    val min_upper_thys = String_Graph.maximals all_upper
    val delete = subtract (op =) min_upper_thys (String_Graph.keys all_upper)      

    val thy_tab =
      Int_Graph.keys graph
      |> filter_out (member (op =) thms_serials)
      |> map (` #theory_long_name o Int_Graph.get_node graph)
      |> filter (member (op =) lower_thys o fst)
      |> filter_out (member (op =) delete o fst)
      |> map (Symtab.map (K single) o Symtab.make o single)
      |> Symtab.joins (K (uncurry append))

    val below =
      lower_bound
      |> Symtab.dest
      |> map_filter (fn (thy_name, opt) => Option.map (pair thy_name o #pos) opt)
      |> maps (fn (thy_name, last) =>
          thy_name 
          |> the o Symtab.lookup thy_tab                               
          |> filter (fn entry => pos_ord (last, (#pos entry)) = GREATER)
          |> map #serial)

    val above =
      min_upper_thys
      |> map (` (#pos o first_entry I o the o Symtab.lookup thys_depd))
      |> maps (fn (first, thy_name) =>
          thy_name
          |> the o Symtab.lookup thy_tab
          |> filter (fn entry => pos_ord ((#pos entry), first) <> LESS)
          |> map #serial)

    fun group_pos thy_entries =
      Inttab.empty
      |> fold
        (fn entry => Inttab.map_default ((pos_line o #pos) entry, []) (curry (op ::) entry))
        thy_entries
      |> Inttab.dest
      |> sort ((int_ord o apply2 fst))
      |> map snd

    val thy_pos = Symtab.map (K group_pos) thy_tab
in (thms_serials, thy_pos, graph, mult, Inttab.make_distinct (map (rpair ()) (below @ above))) end

type dep = {serial: serial, n: int}
val eq_dep = op = o apply2 #serial


(* deps as Ordered association list (opaque) *)

type 'a deps = (serial * 'a) list (* sorted *)
val deps_ord = int_ord o apply2 #1
val dest_deps = map (fn (serial, n) => {serial=serial, n=n})
val dest = I

fun join _ [] _ = []
  | join _ _ [] = []
  | join f (deps1 as (serial1, x1) :: xs1) (deps2 as (serial2, x2) :: xs2) =
      (case int_ord (serial1, serial2) of
        LESS => join f xs1 deps2
      | EQUAL => (serial1, f serial1 x1 x2)::join f xs1 xs2
      | GREATER => join f deps1 xs2)

fun join_outer _ xs [] = xs
  | join_outer _ [] ys = ys
  | join_outer f (deps1 as (serial1, x1) :: xs1) (deps2 as (serial2, x2) :: xs2) =
      (case int_ord (serial1, serial2) of
        LESS => (serial1, x1) :: join_outer f xs1 deps2
      | EQUAL => (serial1, f serial1 x1 x2)::join_outer f xs1 xs2
      | GREATER =>(serial2, x2) :: join_outer f deps1 xs2)

fun map_dep f = map (fn (serial, a) => (serial, f serial a))
fun map_deps f = map (fn (serial, n) => (serial, f {serial=serial, n=n}))

type node = int deps * entry * int deps
val node_serial = #serial o #2
val eq_node = op = o apply2 node_serial

val mk_deps = sort deps_ord o map (fn {serial, n} => (serial, n))
fun build_node_tab graph multiplicity =
  let
    fun mk_dep key n = {serial=key, n=n}
    fun mults f = Int_Graph.Keys.dest #>
      map (fn key => mk_dep key (the (Intreltab.lookup multiplicity (f key)))) #> mk_deps
    fun build_node (key, (entry, (preds, succs))) =
      (key, (mults (rpair key) preds, entry, mults (pair key) succs))
  in Int_Graph.fold (cons o build_node) graph [] |> Inttab.make end

fun build_locations thy_pos infeasible node_tab =
  let
    fun mk_entry {serial, ...} = the (Inttab.lookup node_tab serial)
    fun mk_location (i, entries) = (i, map mk_entry entries)
    fun mk_locations_thy thy_pos_entries =
      let
        val ls = thy_pos_entries |> map_index mk_location
        val feasible = ls |> filter_out (exists (Inttab.defined infeasible o node_serial) o snd)
      in (Inttab.make ls, feasible) end
  in Symtab.map (K mk_locations_thy) thy_pos end

fun build thy ctxt thms =
  let
    val (thms_serials, thy_pos, graph, mult, infeasible) =
      build_deps thy ctxt (build_imports thy) thms
    val node_tab = build_node_tab graph mult
    val thy_pos_tab = build_locations thy_pos infeasible node_tab
    val thms_depss = thms_serials |> map (#3 o the o Inttab.lookup node_tab)
    val thms_deps = fold (join_outer (K Integer.add)) (tl thms_depss) (hd thms_depss)
  in (thms_deps, node_tab, thy_pos_tab) end

fun lookup_thm_pos ctxt thy_pos_tab thm =
  let
    val facts = Proof_Context.facts_of ctxt
    val thm_space = Facts.space_of facts
    val elem = (Name_Space.the_entry thm_space o fst o Thm.get_name_hint) thm
    fun find_pos (pos_tab, poss) =
      Option.map (pair pos_tab) 
        (poss |> find_first (exists (curry (op =) (#serial elem) o node_serial) o snd))
  in Symtab.lookup thy_pos_tab (#theory_long_name elem) |> Option.mapPartial find_pos end

end