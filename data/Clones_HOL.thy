theory Clones_HOL
  imports Complex_Main
begin

declare[[show_sorts,show_types]]

(* categories:

verbatim: verbatim copy
identical: alpha-equivalent copy, e.g. theorem with different name
equivalent: logically equivalent copy, e.g. commuted equality
equal: logically equal copy, e.g. "subset {}" instead of "= {}"
generalization: one generalizes the other, e.g. P x y and P x x
isomorphic: isomorphic but not equal, e.g. due to duplicated constant: P (f x) and Q (f x) but P and Q are equal
shared: same property for different constants, e.g. commutativity of + and *
dual: lemmas dual to each other, e.g. commutativity and associativity 
different: everything else

*)

(* 0.986/verbatim *)
thm Groups.group_cancel.add2
thm Nat.nat_arith.add2

(* 0.986/verbatim *)
thm Groups.group_cancel.add1
thm Nat.nat_arith.add1

(* 0.984/verbatim *)
thm BNF_Def.subst_Pair
thm BNF_Greatest_Fixpoint.subst_Pair

(* 0.983/verbatim *)
thm Product_Type.Collect_case_prodD
thm BNF_Def.Collect_case_prodD

(* 0.979/verbatim *)
thm Groups.group_cancel.rule0
thm Nat.nat_arith.rule0

(* 0.952/equivalent *)
thm Groups.group_cancel.add2
thm Nat.nat_arith.add1

(* 0.952/equivalent *)
thm Groups.group_cancel.add1
thm Nat.nat_arith.add2

(* 0.947/dual *)
thm Complete_Lattices.Sup_Inf_le
thm Enum.finite_Inf_Sup

(* 0.940/equivalent *)
thm Hilbert_Choice.some_eq_ex
thm SMT.verit_sko_ex

(* 0.939/identical *)
thm HOL.True_implies_equals
thm Record.iso_tuple_True_simp

(* 0.936/dual *)
thm Complete_Lattices.Inf_Sup
thm Hilbert_Choice.Sup_Inf

(* 0.931/shared (for different constants) *)
thm Lifting.Quotient_rel
thm Quotient.Quotient3_rel

(* 0.929/identical *)
thm Product_Type.vimage_snd
thm Topological_Spaces.snd_vimage_eq_Times

(* 0.929/identical *)
thm Product_Type.vimage_fst
thm Topological_Spaces.fst_vimage_eq_Times

(* 0.928/generalization *)
thm Complete_Lattices.SUP_const
thm Conditionally_Complete_Lattices.cSUP_const
context complete_lattice begin

interpretation derived: conditionally_complete_lattice
  by (unfold_locales) (auto simp add: Inf_lower Inf_greatest Sup_upper Sup_least)
thm derived.cSUP_const

end

(* 0.928/generalization *)
thm Complete_Lattices.INF_const
thm Conditionally_Complete_Lattices.cINF_const
context complete_lattice begin

interpretation derived: conditionally_complete_lattice
  by (unfold_locales) (auto simp add: Inf_lower Inf_greatest Sup_upper Sup_least)
thm derived.cINF_const

end

(* 0.920/generalization *)
thm Finite_Set.folding_on.infinite
thm Lattices_Big.semilattice_set.infinite

context Lattices_Big.semilattice_set begin

interpretation derived: Finite_Set.folding where f=f and z="the None"
  by (unfold_locales) (simp add: comp_def left_commute)
thm derived.infinite

end


(* 0.915/shared (for different constants) *)
thm Set.the_elem_image_unique
thm Hilbert_Choice.some_elem_image_unique

(* 0.914/shared (for different constants) *)
thm Groups.neg_le_iff_le
thm Boolean_Algebras.compl_le_compl_iff

(* 0.914/shared (for different constants) *)
thm Groups.neg_less_iff_less
thm Boolean_Algebras.compl_less_compl_iff

(* 0.913/generalization *)
thm BNF_Def.rel_funD
thm Transfer.rel_funD2

(* 0.913/isomorphic *)
thm Lattices_Big.semilattice_neutr_set.empty
thm GCD.bounded_quasi_semilattice_set.empty

context Lattices_Big.semilattice_neutr_set begin

interpretation derived: folding_on where f=f and z=z
  by (unfold_locales) (simp add: comp_def left_commute)
thm derived.empty

end

context GCD.bounded_quasi_semilattice_set begin

interpretation derived: folding_on where f=f and z=top
  by (unfold_locales) (simp add: comp_def left_commute)
thm derived.empty

end

(* 0.912/shared (for different constants) *)
thm Lattices.semilattice.left_idem
thm GCD.bounded_quasi_semilattice.left_idem

(* 0.912/shared (for different constants) *)
thm Lattices.semilattice.right_idem
thm GCD.bounded_quasi_semilattice.right_idem

(* 0.911/shared (for different constants) *)
thm Groups.le_imp_neg_le
thm Boolean_Algebras.compl_mono

(* 0.910/shared (for different constants) *)
thm Lifting.Quotient_rel_rep
thm Quotient.Quotient3_rel_rep

(* 0.910/identical (intentional) *)
term \<open>Predicate_Compile.contains\<close>
term \<open>Nunchaku.rmember\<close>

(* 0.908/shared (for different constants) *)
thm Lifting.Quotient_rep_abs
thm Quotient.Quotient3_rep_abs

(* 0.907/equivalent *)
thm Enum.tranclp_unfold
thm Nitpick.tranclp_unfold

(* 0.907/generalization *)
thm Finite_Set.folding_on.infinite
thm Groups_Big.comm_monoid_set.infinite

context Groups_Big.comm_monoid_set begin

interpretation derived: folding where f="f \<circ> g"  
  by (unfold_locales) (simp add: comp_def left_commute)
thm derived.infinite

end

(* 0.906/shared (for different constants) *)
thm Lifting.Quotient_rel_abs
thm Quotient.Quotient3_rel_abs

(* 0.906/dual *)
thm Complete_Lattices.Inf_Sup
thm Enum.finite_Inf_Sup

(* 0.905/generalization *)
thm Finite_Set.folding_on.empty
thm Lattices_Big.semilattice_neutr_set.empty

context Lattices_Big.semilattice_neutr_set begin

interpretation derived: Finite_Set.folding where f=f
  by (unfold_locales) (simp add: comp_def left_commute)
thm derived.empty

end

(* 0.904/dual *)
thm Hilbert_Choice.Sup_Inf
thm Enum.finite_Inf_Sup

(* 0.903/equal *)
thm Nat.mult_is_0
thm GCD.lcm_0_iff_nat

(* 0.896/generalization *)
thm Finite_Set.folding_on.empty
thm Groups_Big.comm_monoid_set.empty

context Groups_Big.comm_monoid_set begin
interpretation derived: Finite_Set.folding where f="f \<circ> g"
  by (unfold_locales) (simp add: comp_def left_commute)
thm derived.empty

end

(* 0.896/shared (for different constants) *)
thm Lifting.Quotient_refl2
thm Quotient.Quotient3_refl2

(* 0.896/shared (for different constants) *)
thm Lifting.Quotient_refl1
thm Quotient.Quotient3_refl1

(* 0.895/shared (for different constants) *)
thm Lifting.apply_rsp
thm Quotient.apply_rspQ3

(* 0.894/different *)
term \<open>Set.pairwise\<close>
term \<open>Relation.asymp_on\<close>

(* 0.894/identical *)
thm BNF_Def.comp_apply_eq
thm Fun_Def.comp_cong

(* 0.892/different *)
thm Complete_Lattices.Sup_Inf_le
thm Hilbert_Choice.Sup_Inf

(* 0.889/shared (for different constants) *)
thm Lifting.Quotient_abs_rep
thm Quotient.Quotient3_abs_rep

(* 0.889/shared (for different constants) *)
thm Lifting.Quotient_refl2
thm Quotient.Quotient3_refl1

(* 0.889/shared (for different constants) *)
thm Lifting.Quotient_refl1
thm Quotient.Quotient3_refl2

(* 0.889/shared (for different types) *)
thm Real_Vector_Spaces.metric_LIM_compose2
thm Limits.LIM_compose2

(* 0.888/shared (for different constants) *)
thm Lifting.Quotient_rep_reflp
thm Quotient.Quotient3_rep_reflp

(* 0.886/dual *)
thm Real_Vector_Spaces.tendsto_at_topI_sequentially
thm Limits.tendsto_at_botI_sequentially

(* 0.886/different *)
thm HOL.arg_cong
thm Hilbert_Choice.bijection.eqI

(* 0.885/identical *)
thm Nat.antimono_iff_le_Suc
thm Topological_Spaces.decseq_Suc_iff

(* 0.885/identical *)
thm Nat.mono_iff_le_Suc
thm Topological_Spaces.incseq_Suc_iff

(* 0.883/different *)
thm Boolean_Algebras.boolean_algebra.conj_zero_left
thm GCD.bounded_quasi_semilattice.bottom_right_bottom

(* 0.883/shared *)
thm Boolean_Algebras.boolean_algebra.conj_zero_right
thm GCD.bounded_quasi_semilattice.bottom_right_bottom

(* 0.882/dual *)
thm Groups.add_nonneg_nonneg
thm Rings.mult_nonneg_nonneg

(* 0.881/equal *)
thm Set.equals0I
thm BNF_Least_Fixpoint.subset_emptyI

(* 0.880/equivalent *)
thm HOL.if_cong
thm SMT.verit_if_cong

(* 0.878/dual *)
thm Groups.add_nonpos_nonpos
thm Rings.mult_nonneg_nonpos

(* 0.878/dual *)
thm Groups.add_nonpos_nonpos
thm Rings.mult_nonpos_nonneg

(* 0.878/dual *)
thm Groups.add_nonpos_nonpos
thm Rings.mult_nonneg_nonpos2

(* 0.878/shared (for different constants) *)
thm Groups.minus_minus
thm Boolean_Algebras.double_compl

(* 0.876/shared *)
thm Boolean_Algebras.abstract_boolean_algebra_sym_diff.xor_one_left
thm GCD.bounded_quasi_semilattice.top_right_normalize

(* 0.876/shared *)
thm Boolean_Algebras.abstract_boolean_algebra_sym_diff.xor_one_right
thm GCD.bounded_quasi_semilattice.top_left_normalize

(* 0.875/shared *)
term Order_Relation.Well_order
term BNF_Cardinal_Order_Relation.Card_order

(* 0.875/shared *)
term Order_Relation.Linear_order
term BNF_Cardinal_Order_Relation.Card_order

(* 0.875/shared *)
term Order_Relation.Total
term BNF_Cardinal_Order_Relation.Card_order

(* 0.875/shared *)
term Order_Relation.Partial_order
term BNF_Cardinal_Order_Relation.Card_order

(* 0.875/shared *)
term Order_Relation.Preorder
term BNF_Cardinal_Order_Relation.Card_order

(* 0.875/shared *)
term Order_Relation.Refl
term BNF_Cardinal_Order_Relation.Card_order

(* 0.874/dual *)
thm Groups.add_neg_neg
thm Rings.mult_pos_neg

(* 0.874/dual *)
thm Groups.add_neg_neg
thm Rings.mult_neg_pos

(* 0.874/dual *)
thm Groups.add_neg_neg
thm Rings.mult_pos_neg2

(* 0.874/dual *)
thm Groups.add_pos_pos
thm Rings.mult_pos_neg

(* 0.874/dual *)
thm Groups.add_pos_pos
thm Rings.mult_neg_pos

(* 0.874/dual proeprty *)
thm Groups.add_pos_pos
thm Rings.mult_pos_neg2

(* 0.874/generalization *)
term Finite_Set.folding_on.F
term Lattices_Big.semilattice_neutr_set.F

context Lattices_Big.semilattice_neutr_set begin

interpretation derived: Finite_Set.folding where f=f
  by (unfold_locales) (simp add: comp_def left_commute)

lemma "derived.F = F"
  unfolding eq_fold derived.eq_fold by simp

end

(* 0.873/isomorphic *)
thm Groups_Big.comm_monoid_set.remove
thm Lattices_Big.semilattice_neutr_set.remove

context Groups_Big.comm_monoid_set begin

interpretation derived: folding where f="f \<circ> g"  
  by (unfold_locales) (simp add: comp_def left_commute)

thm derived.remove

end

context Lattices_Big.semilattice_neutr_set begin

interpretation derived: Finite_Set.folding where f=f
  by (unfold_locales) (simp add: comp_def left_commute)

thm derived.remove

end

(* 0.873/equivalent (intentional) *)
thm HOL.induct_conj_curry
thm BNF_Fixpoint_Base.conj_imp_eq_imp_imp

(* 0.872/identical *)
thm HOL.conj_left_cong
thm Record.refl_conj_eq

(* 0.872/isomorphic *)
thm Relation.single_valuedp_iff_Uniq
thm Transfer.right_unique_iff

lemma "single_valuedp = right_unique"
  unfolding single_valuedp_def right_unique_def by blast

(* 0.871/generalization *)
thm Finite_Set.folding_on.empty
thm GCD.bounded_quasi_semilattice_set.empty

context GCD.bounded_quasi_semilattice_set begin

interpretation derived: folding_on where f=f and z=top
  by (unfold_locales) (simp add: comp_def left_commute)
thm derived.empty

end

(* 0.871/isomorphic *)
thm HOL.induct_forall_eq
thm Transfer.transfer_forall_eq

(* 0.871/dual *)
thm Fun.the_inv_into_comp
thm Hilbert_Choice.inv_into_comp

(* 0.870/dual *)
thm Groups.add_nonpos_nonpos
thm Rings.mult_nonpos_nonpos

(* 0.870/dual *)
thm Complete_Lattices.dual_complete_lattice
thm Hilbert_Choice.dual_complete_distrib_lattice

(* 0.870/different *)
term Relation.symp_on
term Complete_Partial_Order.chain

(* 0.870/dual *)
thm BNF_Def.rel_funD
thm Transfer.rel_funE

(* 0.869/identical *)
thm Set.eq_mem_trans
thm BNF_Composition.ssubst_mem

(* 0.868/isomorphic *)
thm Relation.single_valuedp_iff_Uniq
thm Transfer.left_unique_iff

lemma "single_valuedp = right_unique"
  unfolding single_valuedp_def right_unique_def by blast

(* 0.868/identical (intentional) *)
term Meson.skolem
term Metis.select

(* 0.868/identical (intentional) *)
term Meson.skolem
term Metis.lambda

(* 0.868/identical (intentional) *)
term Fun.id
term Meson.skolem

(* 0.868/identical (intentional) *)
term Fun.id
term Metis.select

(* 0.868/identical (intentional) *)
term Fun.id
term Metis.lambda

(* 0.867/dual *)
thm Boolean_Algebras.abstract_boolean_algebra_sym_diff.xor_self
thm GCD.bounded_quasi_semilattice.bottom_right_bottom

(* 0.867/dual *)
thm Groups.add_neg_neg
thm Rings.mult_neg_neg

(* 0.867/dual *)
thm Groups.add_pos_pos
thm Rings.mult_neg_neg

(* 0.866/different *)
thm Groups.group.inverse_neutral
(* Boolean_Algebra.<unnamed>.compl_zero *)

(* 0.864/shared (for different constants) *)
thm Lifting.apply_rsp''
thm Quotient.apply_rspQ3''

(* 0.864/dual (for different constants) *)
thm Lattices.semilattice.left_idem
thm GCD.bounded_quasi_semilattice.right_idem

(* 0.862/different *)
thm Boolean_Algebras.boolean_algebra.conj_cancel_left
thm GCD.bounded_quasi_semilattice.top_right_normalize

end