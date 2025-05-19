signature LOCATOR =
sig
  type node = Relocate_Deps.node
  type location = {pos: int, node: node}
  type result =
    {fit: real, location: location, locations: location list, deps: real Relocate_Deps.deps}
  (* Ranking *)
  type Ranking
  val top_ranking: int -> Ranking
  val from_ranking: result -> Ranking
  val min_score: Ranking -> real
  val insert: result -> Ranking -> Ranking
  val dest: Ranking -> result list
  (* Multiplicity *)
  type Multiplicity
  val singleton: Multiplicity
  val multiples: Multiplicity
  val multiplog: Multiplicity
  (* Relevance *)
  type Relevance
  val unit_relevance: Relevance
  val IF_relevance: Multiplicity -> Relevance
  val oIF_relevance: real -> Multiplicity -> Relevance
  val IDF_relevance: Relevance
  val pow_relevance: int -> Relevance -> Relevance
  val kind_relevance: {typ: real, class: real, thm: real, const: real} -> Relevance -> Relevance
  (* Density *)
  type Density
  val unit_density: Density
  val weighted_density: (Multiplicity * Relevance) -> Density
  val pow_density: int -> Density -> Density
  (* Config *)
  type config
  val prepare: node Inttab.table -> Multiplicity * Relevance * Density -> config
  (* Locate *)
  type Locator
  val locate: int Relocate_Deps.deps -> config * Locator -> node list Inttab.table ->
    (int * node list) list -> Ranking -> Ranking
  val single: Locator
  val restricted: {limit: int, precise: bool} -> {dist_pow: real} -> Locator
  val community: {dist_pow: real} -> Locator
end

structure Locator: LOCATOR =
struct
type node = Relocate_Deps.node

fun pow 0 _ = 1.0 | pow n r = r * pow (n - 1) r
fun real_sum (f: 'a -> real) xs = fold (fn a => fn r => r + f a) xs 0.0

type location = {pos: int, node: node}
type result = 
  {fit: real, location: location, locations: location list, deps: real Relocate_Deps.deps}

fun fast_lookup (tab: real Inttab.table) =
  let fun cons1 x xs = case xs of [] => [x] | [y] => if Real.== (x,y) then [x] else [x,y] | _ => xs
  in case (Inttab.fold (cons1 o snd) tab []) of [x] => K x | _ => the o Inttab.lookup tab end


(** Ranking **)

type Ranking = {min_score: result list -> real, norm: result list -> result list, xs: result list}

fun min_score {min_score, xs, ...} = min_score xs
fun dest {xs, ...} = rev xs

local

val ord =
 (prod_ord Real.compare Int.compare) o apply2 
   (fn {fit, location={node, ...}, ...} => (fit, Relocate_Deps.node_serial node))

in

fun insert x {norm, min_score, xs} = 
  {norm=norm, min_score=min_score, xs=norm (Ord_List.insert ord x xs)}

end

fun top_ranking n =
  {min_score=fn xs => if length xs < n orelse null xs then Real.negInf else #fit (hd xs), 
   norm=fn xs => drop (length xs - n) xs, xs=[]}

fun from_ranking result =
  {min_score=K (#fit result), norm=fn xs => if #fit (hd xs) < #fit result then tl xs else xs, xs=[]}


(** Sums **)

type Multiplicity = (real * int) -> real

val singleton = fst
fun multiples (r, i) = r * real i
fun multiplog (r, i) = r * (1.0 + Math.ln (real i))


(** Relevance **)

type Relevance = int -> node -> real

val unit_relevance = K (K 1.0)
fun oIF_relevance offset mult _ (preds, _, _) =
  (1.0 + offset) / (offset + real_sum (mult o pair 1.0 o #n) (Relocate_Deps.dest_deps preds))
val IF_relevance = oIF_relevance 0.0
fun IDF_relevance N (preds, _, _) = Math.ln (real N / (Relocate_Deps.dest preds |> length |> real))
fun pow_relevance n r = pow n oo r

local

val classN = Name_Space.kind_of (Sign.class_space @{theory})
val typN = Name_Space.kind_of (Sign.type_space @{theory})
val constN = Name_Space.kind_of (Sign.const_space @{theory})
val thmN = Name_Space.kind_of (Facts.space_of (Proof_Context.facts_of @{context}))

in

fun kind_relevance {typ: real, class: real, thm: real, const: real} r i node =
  let
    val kind = #kind (#2 node)
    val fac =
      if kind = classN then class
      else if kind = typN then typ
      else if kind = constN then const
      else if kind = thmN then thm
      else error ("Invalid kind: " ^ quote kind)
  in fac * r i node end

end


(** Density **)

type Density = 
  {deps_total_relv: Relevance,
   deps_total: Relevance -> (serial -> node) -> int -> node -> real}

val unit_density =
   {deps_total_relv=K (K 1.0), deps_total=K (K (K (K 1.0)))}
fun weighted_density (mult, relv) =
  {deps_total_relv=relv,
   deps_total=
    fn relv => fn the_node => fn N =>
      real_sum (fn {serial, n} => mult (relv N (the_node serial), n)) o
        Relocate_Deps.dest_deps o #3}

fun pow_density n {deps_total_relv, deps_total} =
   {deps_total_relv=deps_total_relv, deps_total=pow n oooo deps_total}


(** Cache **)

type config = Multiplicity * (serial -> real) * (serial -> real)

fun cache_relevance N node_tab relv = fast_lookup (Inttab.map (K (relv N)) node_tab)
fun cache_density N node_tab {deps_total_relv, deps_total} =
  let
    val deps_total_relv = cache_relevance N node_tab deps_total_relv
  in
    fast_lookup (Inttab.map (K (deps_total (K (deps_total_relv o Relocate_Deps.node_serial))
      (the o Inttab.lookup node_tab) N)) node_tab)
  end

fun prepare node_tab (mult: Multiplicity, relv: Relevance, dens: Density) =
  let
    val N = Inttab.size node_tab
    val relv = cache_relevance N node_tab relv
    val dens = cache_density N node_tab dens
  in (mult, relv, dens) end


(** Locator **)

type Locator =
  {f: config -> int Relocate_Deps.deps -> node list Inttab.table -> (int * node list) -> Any.T ->
    Ranking -> result list,
   prep_thy: config -> node list Inttab.table -> Any.T}

fun locate deps_i (config, locator) pos_tab locations =
  let
    val prepared = #prep_thy locator config pos_tab
    fun best a b = if #fit a < #fit b then b else a
    fun rank_location (i, nodes) ranking =
      case #f locator config deps_i pos_tab (i, nodes) prepared ranking of
        [] => ranking | result::results => insert (fold best results result) ranking 
  in fold rank_location locations end

exception Single
val single =
  {f=fn (mult, relv, dens) => fn i_deps => K (fn (j, j_nodes) => K (K
    let
      fun rank j (j_node as (_, _, j_deps)) =
        let
          val j_serial = Relocate_Deps.node_serial j_node
          fun relv_total k_serial j_n i_n =
            (relv k_serial / dens j_serial, Integer.min j_n i_n)
          val joined = Relocate_Deps.join relv_total j_deps i_deps
          val deps = joined |> Relocate_Deps.map_dep (K mult)
          val fit = joined |> Relocate_Deps.dest |> real_sum (mult o snd)
          val location = {pos=j, node=j_node}
        in {fit=Real.checkFloat fit, location=location, locations=[location], deps=deps} end
    in map (rank j) j_nodes end)),
   prep_thy=K (K Single)}

fun check_total dens (_, {serial, ...}, deps) = if null deps then 0.0 else 1.0 / dens serial

exception Restricted of (int * real) list
fun f_restricted limit precise dist_pow (mult, relv, dens) i_deps pos_tab (j, j_nodes)
   pos_count_total ranking =
  let
    fun best a b = if #fit a < #fit b then b else a
    fun distance pos = Math.pow (real (1 + abs (pos - j)), dist_pow)
    fun dist min max = Math.pow (real (1 + abs (max - min)), dist_pow)
    fun rank pos_tab thy_sum j (j_node as (_, _, j_deps)) =
      let
        fun total node = 1.0 / (dens (Relocate_Deps.node_serial node))

        fun prepare_pos (l, l_nodes) =
          let
            fun prepare_node l_node =
              if null (#3 l_node) then NONE
              else SOME (total l_node, l_node)
            val res = map_filter prepare_node l_nodes
          in if null res then NONE else SOME 
            (distance l, fold (curry Real.max o fst) (tl res) (fst (hd res)), (l, res))
          end
        fun accum_max_total e [] = [e]
          | accum_max_total (distance, max_total, nodes) ((x as (_, max_total1, _))::xs) =
            (distance, Real.max (max_total, max_total1), nodes)::x:: xs
        val total_dist_dep_poss =
          (Inttab.dest pos_tab
          |> map_filter prepare_pos
          |> sort (Real.compare o apply2 #1)
          |> fold_rev accum_max_total) []
        fun del _ [] = [] | del l ((x as (_, _, (k, _)))::xs) = if k = l then xs else x::del l xs

        fun fit dist total_sum deps_relvs =
          (real_sum (mult o snd) (Relocate_Deps.dest deps_relvs) * total_sum) / dist

        val init = 
          let
            val dist = dist j j
            fun dep_relvs serial = relv serial
            val deps_relvs =
              Relocate_Deps.join (fn serial => pair (dep_relvs serial) oo Integer.min) i_deps j_deps
            val total_sum = total j_node
            val locations = [{pos=j, node=j_node}]
          in
            {fit=fit dist total_sum deps_relvs, min=j, max=j, dist=dist, total_sum=total_sum,
             deps_relvs=deps_relvs, locations=locations}
          end

        fun add {locations, deps_relvs, min, max, total_sum, ...} l (l_total, l_node as (_, _, l_deps)) =
          let
            val deps_relvs = Relocate_Deps.join (K (apsnd o Integer.min)) l_deps deps_relvs
            val min = Integer.min min l
            val max = Integer.max max l
            val dist = dist min max
            val total_sum = total_sum + l_total
            val location = {pos=l, node=l_node}
            val locations = location::locations
          in
            {fit=fit dist total_sum deps_relvs, min=min, max=max, dist=dist, total_sum=total_sum,
             deps_relvs=deps_relvs, locations=locations}
          end

        fun mk_result {fit, locations, deps_relvs, ...} =
          {fit=Real.checkFloat fit, location={pos=j, node=j_node},
           locations=map (fn {pos, node, ...} => {pos=pos, node=node}) locations,
           deps=Relocate_Deps.map_dep (K mult) deps_relvs}

        fun rescale {fit, dist, ...} dist1 = fit * (dist / dist1)

        fun delta_rec poss thy_sum current =
          let
            val deps_relvs = #deps_relvs current
            val deps_sum =
              real_sum (fn (_, (relvs, n)) => mult (relvs, n)) (Relocate_Deps.dest deps_relvs)
            (* approximation: what if we added all, without changing intersection /
                 only taking individual distances instead of set distance *)
            val is_beatable = #fit current + (thy_sum * deps_sum) >= min_score ranking

            fun add_bests [] result = result
              | add_bests ((distance, max_total, (l, l_dnodes))::xs) result =
                let
                  val dist1 = dist (Integer.min (#min current) l) (Integer.max (#max current) l)
                  fun add_best (l_total, l_node) result =
                    (* approximation: ignores decreasing intersection *)
                    if rescale current dist1 + ((l_total * deps_sum) / dist1) < #fit result
                    then result
                    else best result (add current l (l_total, l_node))
                in
                  (* approximation: what if we added something with max total that is further away? *)
                  if rescale current distance + ((max_total * deps_sum) / distance) < #fit result
                  then result
                  else add_bests xs (fold add_best l_dnodes result)
                end
          in
            if null poss orelse limit = length (#locations current) orelse not is_beatable then
              mk_result current
            else if not precise andalso #fit current >= min_score ranking then mk_result current
            else
              let val next = add_bests poss current
              in
                if limit = length (#locations next) orelse not (#fit next > #fit current) then
                  mk_result next
                else
                  let
                    val {pos, node, ...} = next |> #locations |> hd
                    val thy_sum1 = thy_sum - (check_total dens node / distance pos)
                  in delta_rec (del pos poss) thy_sum1 next end
            end
          end

      in delta_rec total_dist_dep_poss thy_sum init end

    val factors =
      map (fn (l, count_total) => if l = j then 0.0 else count_total / distance l) pos_count_total
    val thy_sum =
      real_sum I ((if limit < 1 then I else take limit o sort (rev_order o Real.compare)) factors)
  in map (rank (Inttab.delete j pos_tab) thy_sum j) (filter_out (null o #3) j_nodes) end

fun restricted {limit, precise} {dist_pow} =
  {f=fn config => fn i_deps => fn pos_tab => fn pos =>
     fn (Restricted pos_count_total) => f_restricted limit precise dist_pow config i_deps pos_tab
      pos pos_count_total,
   prep_thy=fn (_, _, dens) => fn pos_tab =>
    Restricted
      (map (apsnd (fn nodes => fold (curry Real.max o check_total dens) nodes 0.0))
        (Inttab.dest pos_tab))}

val community = restricted {limit=0,precise=true}

end
