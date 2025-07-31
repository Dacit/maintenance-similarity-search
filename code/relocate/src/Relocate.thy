theory Relocate
  imports Pure
  keywords "relocate" :: diag and "ranking" "suggest"
begin

ML_file \<open>relocate_deps.ML\<close>
ML_file \<open>locator.ML\<close>
ML_file \<open>relocate.ML\<close>

ML \<open>
val _ = Outer_Syntax.command \<^command_keyword>\<open>relocate\<close> "relocate"
  (Parse.thms1 -- 
    (Parse.!!! (Scan.optional (Parse.$$$ "ranking" |-- Parse.thm >> SOME) NONE) --
     Parse.!!! (Scan.optional (Parse.$$$ "suggest" |-- Parse.nat) 1))
     >> (fn (args, (ranking, suggest)) => Toplevel.keep (fn st =>
    if suggest < 1 then writeln "No suggestion" else
    let
      val thy = Toplevel.theory_of st
      val ctxt = Toplevel.context_of st
      val consider = Option.map (the_single o Attrib.eval_thms ctxt o single) ranking
      val thms = Attrib.eval_thms ctxt args
      val _ = Relocate.relocate thy ctxt {max=suggest, verbose=false} consider thms
    in () end)))
\<close>

end