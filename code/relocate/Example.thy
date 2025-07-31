theory Example
  imports Main Relocate.Relocate
begin

text \<open>Standard usage\<close>
relocate nth_append_right

text \<open>Suggest more than one option\<close>
relocate nth_append_right suggest 2

text \<open>Return ranking for a user-supplied suggestion (computationally expensive)\<close>
relocate nth_append_right ranking nth_append_left

end