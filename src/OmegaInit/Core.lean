module
public import Init.Core
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Exists Iff Nat.succ.inj Ne Ne.intro Ne.irrefl Ne.symm Not.elim Not.imp Not.intro Sum and_comm apply_eqRec cast_eq cast_heq eagerReduce eqRec_heq eqRec_heq_iff eq_comm eq_self_iff_true false_iff_true false_imp_iff false_ne_true false_of_ne false_of_true_eq_false false_of_true_iff_false flip flip.eq_1 flip_flip heq_comm heq_eqRec_iff heq_of_eqRec_eq heq_of_eq_of_heq heq_of_heq_of_eq heq_self_iff_true id.eq_1 id_def if_neg if_pos iff_comm iff_def iff_def' iff_false_intro iff_false_left iff_false_right iff_iff_implies_and_implies iff_not_self iff_of_eq iff_of_false iff_of_true iff_true_intro iff_true_left iff_true_right imp_congr imp_congr_ctx imp_congr_left imp_congr_right imp_false imp_iff_not imp_iff_right imp_imp_imp imp_intro imp_not_comm imp_not_self imp_self imp_true_iff inline inline.eq_1 ite_eq_left ite_eq_right mt ne_comm ne_false_of_self ne_self_iff_false ne_true_of_not neq_of_not_iff not_congr not_false not_false_iff not_iff_false_intro not_not_intro not_not_not not_not_of_not_imp not_of_iff_false not_of_not_imp not_true of_iff_true optParam_eq or_comm proof_irrel trivial true_eq_false_of_false true_iff_false true_imp_iff true_ne_false type_eq_of_heq)
end Omega
namespace Omega.And
export _root_.And (comm elim symm)
end Omega.And
namespace Omega.Bool
export _root_.Bool (of_not_eq_false of_not_eq_true)
end Omega.Bool
namespace Omega.Empty
export _root_.Empty (elim)
end Omega.Empty
namespace Omega.Eq
export _root_.Eq (comm mp mpr ndrecOn substr to_iff)
end Omega.Eq
namespace Omega.Exists
export _root_.Exists (casesOn elim intro rec recOn)
end Omega.Exists
namespace Omega.Function
export _root_.Function (comp_apply comp_const comp_def comp_id const_apply const_comp false_comp id_comp true_comp)
end Omega.Function
namespace Omega.HEq
export _root_.HEq (comm ndrec ndrecOn subst symm trans)
end Omega.HEq
namespace Omega.Iff
export _root_.Iff (casesOn comm elim intro mp mpr of_eq rec recOn refl rfl symm trans)
end Omega.Iff
namespace Omega.Lean
export _root_.Lean (injEq_helper)
end Omega.Lean
namespace Omega.Nat
export _root_.Nat (add_zero)
end Omega.Nat
namespace Omega.Or
export _root_.Or (comm symm)
end Omega.Or
namespace Omega.PEmpty
export _root_.PEmpty (elim)
end Omega.PEmpty
namespace Omega.PUnit
export _root_.PUnit (eq_punit ext subsingleton)
end Omega.PUnit
namespace Omega.Sum
export _root_.Sum (casesOn inl inr nonemptyLeft nonemptyRight rec recOn)
end Omega.Sum
namespace Omega.imp
export _root_.imp (swap)
end Omega.imp
