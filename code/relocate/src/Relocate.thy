theory Relocate
  imports Pure
  keywords "relocate" :: diag
begin

ML_file \<open>relocate_deps.ML\<close>
ML_file \<open>locator.ML\<close>
ML_file \<open>relocate.ML\<close>

ML \<open>
val _ = Outer_Syntax.command \<^command_keyword>\<open>relocate\<close> "relocate"
  (Parse.thms1 -- Parse.!!! (Scan.optional (Parse.$$$ "for" |-- Parse.thm >> SOME) NONE)
     >> (fn (args, arg) => Toplevel.keep (fn st => 
    let
      val thy = Toplevel.theory_of st
      val ctxt = Toplevel.context_of st
      val consider = Option.map (the_single o Attrib.eval_thms ctxt o single) arg
      val thms = Attrib.eval_thms ctxt args
      val _ = Relocate.relocate thy ctxt {max=1, verbose=false} consider thms
    in () end)))
\<close>

end