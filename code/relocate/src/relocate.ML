signature RELOCATE =
sig
  structure Locator: LOCATOR
  type result =
    {setup: Timing.timing,
     search: Timing.timing,
     thms: string list,
     suggested: (string * int * real) list,
     total: int}
  val relocate: theory -> Proof.context -> {max: int, verbose: bool} -> thm option -> thm list ->
    result
end

structure Relocate: RELOCATE =
struct
structure Locator = Locator
type result =
  {setup: Timing.timing,
   search: Timing.timing,
   thms: string list,
   suggested: (string * int * real) list,
   total: int}


(* compatibility with older versions *)

val Timing_zero = {elapsed = Time.zeroTime, cpu = Time.zeroTime, gc = Time.zeroTime}


(* pretty *)

fun pretty_ranked_nodes verbose elems =
  elems
  |> sort (make_ord ((op >) o apply2 snd))
  |> map (fn (node, w) =>
    Pretty.block (Relocate_Deps.pretty_entry (#2 node) ::
      (if verbose then [Pretty.str (" (" ^ (string_of_real w) ^ ")")] else [])))
  |> map (Pretty.item o single)
  |> Pretty.chunks


(* relocate *)

fun empty setup_timing thms_names = 
  {setup = setup_timing, search = Timing_zero, thms = thms_names, suggested = [], total = 0}

fun relocate thy ctxt {max, verbose} suggestion thms =
  let
    val thms_names = map (Thm_Name.print o Thm.get_name_hint) thms

    val (setup_timing, (thms_deps, node_tab, thy_pos_tab)) =
      Timing.timing (Relocate_Deps.build thy ctxt) thms
    
    val num_options = Symtab.fold (curry (op +) o length o snd o snd) thy_pos_tab 0
    val init_pos = the_list suggestion |> map (Relocate_Deps.lookup_thm_pos ctxt thy_pos_tab)
   in
    if exists is_none init_pos then (writeln "Suggestion invalid"; empty setup_timing thms_names)
    else if null (Relocate_Deps.dest thms_deps) then
      (writeln "No shared dependencies"; empty setup_timing thms_names)
    else if num_options = 0 then (writeln "No other position found"; empty setup_timing thms_names)
    else
      let
        val relevance =
          Locator.kind_relevance {typ=0.01, class=0.01, thm=0.01, const=0.02} Locator.IDF_relevance
        val config =
          Locator.prepare node_tab
            (Locator.multiplog,
             Locator.pow_relevance 2 relevance,
             Locator.weighted_density (Locator.multiplog, relevance))

        val _ = writeln ("Finding best position out of " ^ (Value.print_int num_options) ^ " ...")

        fun find_pos c = Locator.locate thms_deps (config, Locator.restricted c {dist_pow=0.85})
        fun find n = Symtab.fold (uncurry (find_pos {limit=n, precise=true}) o snd) thy_pos_tab

        val init =
          (Locator.top_ranking 1)
          |> fold ((fn (pos_tab, pos) =>
              find_pos {limit=10, precise=false} pos_tab [pos]) o the) init_pos
          |> Locator.dest

        val ranking = Locator.from_ranking (Library.the_single
          (case init of [] => find 3 (Locator.top_ranking 1) |> Locator.dest | x::xs => 
             (if verbose then writeln ("Suggestion result: " ^ string_of_real (#fit x)) else ();
              x::xs)))

        val (timing, ranking) = Timing.timing (find 10) ranking
        val suggested = Locator.dest ranking

        val _ =
          if is_none suggestion orelse null init then () 
          else writeln ("Suggestion ranked #" ^ (string_of_int (length suggested)))

        val the_node = the o (Inttab.lookup node_tab)
        fun print_suggested {location={node, ...}, fit, locations, deps} =
          let
            val deps = Relocate_Deps.dest deps |> map (apfst the_node)
            val locs = locations
              |> map (fn l => (#node l, ~(real (#pos l))))
            val _ = Pretty.writeln_chunks (
              [Pretty.block
                [Pretty.str "Consider ", Relocate_Deps.pretty_entry (#2 node),
                  Pretty.str (" (" ^ (string_of_real fit) ^ "), since it shares:")],
                pretty_ranked_nodes verbose deps] @
              ([Pretty.str " with: ", pretty_ranked_nodes false locs]))
           in () end

        val _ = suggested |> (if max = 0 then I else take max) |> map print_suggested
        fun result {location={pos, node}, fit, ...} = (#name (#2 node), pos, fit)
      in
        {setup = setup_timing,
         search = timing,
         thms = thms_names,
         suggested = map result suggested,
         total = num_options}
      end
    end
end