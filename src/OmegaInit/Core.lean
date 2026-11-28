module
public import Init.Core
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Decidable.byCases.match_1 DoResultBC DoResultBC.break.elim DoResultBC.continue.elim DoResultPR DoResultPR.pure.elim DoResultPR.return.elim DoResultPRBC DoResultPRBC.break.elim DoResultPRBC.continue.elim DoResultPRBC.pure.elim DoResultPRBC.return.elim DoResultSBC DoResultSBC.break.elim DoResultSBC.continue.elim DoResultSBC.pureReturn.elim Equivalence Exists ForIn ForIn' ForInStep ForInStep.done.elim ForInStep.yield.elim HasEquiv Iff InvImage LawfulBEq Nat.succ.inj Ne Ne.intro Ne.irrefl Ne.symm NonScalar Not.elim Not.imp Not.intro PNonScalar PSigma PSum PSum.inl.elim PSum.inr.elim Quot.exists_rep Quot.hrecOn Quot.indBeta Quot.indep Quot.inductionOn Quot.liftBeta Quotient Quotient.exists_rep Quotient.hrecOn Quotient.ind Quotient.inductionOn Quotient.inductionOn₂ Quotient.inductionOn₃ Quotient.ind₂ Quotient.lift Quotient.liftOn Quotient.liftOn₂ Quotient.lift₂ Quotient.mk Quotient.mk' ReflBEq Setoid Sigma Squash Squash.ind Squash.lift Squash.mk Subsingleton Subtype.instDecidableEq.match_1 Sum Sum.inl.elim Sum.inl.noConfusion Sum.inr.elim Sum.inr.noConfusion Thunk and_comm apply_eqRec bne cast_eq cast_heq decidable_of_decidable_of_eq decidable_of_decidable_of_iff decidable_of_decidable_of_iff.match_1 dite_eq_left dite_eq_right eagerReduce eqRec_heq eqRec_heq_iff eq_comm eq_self_iff_true equivalence_true false_iff_true false_imp_iff false_ne_true false_of_ne false_of_true_eq_false false_of_true_iff_false flip flip.eq_1 flip_flip heq_comm heq_eqRec_iff heq_of_eqRec_eq heq_of_eq_of_heq heq_of_heq_of_eq heq_self_iff_true id.eq_1 id_def if_neg if_pos iff_comm iff_def iff_def' iff_false_intro iff_false_left iff_false_right iff_iff_implies_and_implies iff_not_self iff_of_eq iff_of_false iff_of_true iff_true_intro iff_true_left iff_true_right imp_congr imp_congr_ctx imp_congr_left imp_congr_right imp_false imp_iff_not imp_iff_right imp_imp_imp imp_intro imp_not_comm imp_not_self imp_self imp_true_iff inline inline.eq_1 instBEqOption instBEqOption.beq instBEqProd instDecidableDite instDecidableEqEmpty instDecidableEqOfLawfulBEq instDecidableEqOfLawfulBEq.match_1 instDecidableEqPEmpty instDecidableEqPSigma instDecidableEqPSigma.match_1 instDecidableEqPSigma.match_3 instDecidableEqPSigma.match_5 instDecidableEqPUnit instDecidableEqProd instDecidableEqProd.match_1 instDecidableEqProd.match_3 instDecidableEqSigma instDecidableEqSigma.match_1 instDecidableEqSigma.match_3 instDecidableEqSigma.match_5 instDecidableEqSum instDecidableEqSum.decEq instDecidableEqSum.decEq.match_1 instDecidableFalse instDecidableIff instDecidableIff.match_1 instDecidableTrue instHasEquivOfSetoid instInhabitedForInStep instInhabitedForInStep.default instInhabitedMProd instInhabitedNonScalar instInhabitedNonScalar.default instInhabitedPNonScalar instInhabitedPNonScalar.default instInhabitedPProd instInhabitedPUnit instInhabitedProd instInhabitedProp instInhabitedThunk instInhabitedTrue instInhabitedTrue.default instTransIff iteInduction ite_eq_left ite_eq_right mt ne_comm ne_false_of_self ne_self_iff_false ne_true_of_not neq_of_not_iff noConfusionEnum noConfusionTypeEnum not_congr not_eq_of_beq_eq_false not_false not_false_iff not_iff_false_intro not_not_intro not_not_not not_not_of_not_imp not_of_iff_false not_of_not_imp not_true of_iff_true optParam_eq or_comm proof_irrel strictAnd strictOr toBoolUsing trivial true_eq_false_of_false true_iff_false true_imp_iff true_ne_false type_eq_of_heq)
end Omega
namespace Omega.And
export _root_.And (comm elim symm)
end Omega.And
namespace Omega.BEq
export _root_.BEq (rfl)
end Omega.BEq
namespace Omega.Bool
export _root_.Bool (of_not_eq_false of_not_eq_true)
end Omega.Bool
namespace Omega.Decidable
export _root_.Decidable (byCases em)
end Omega.Decidable
namespace Omega.DoResultBC
export _root_.DoResultBC (casesOn ctorElim ctorElimType ctorIdx rec recOn «break» «continue»)
end Omega.DoResultBC
namespace Omega.DoResultPR
export _root_.DoResultPR (casesOn ctorElim ctorElimType ctorIdx pure rec recOn «return»)
end Omega.DoResultPR
namespace Omega.DoResultPRBC
export _root_.DoResultPRBC (casesOn ctorElim ctorElimType ctorIdx pure rec recOn «break» «continue» «return»)
end Omega.DoResultPRBC
namespace Omega.DoResultSBC
export _root_.DoResultSBC (casesOn ctorElim ctorElimType ctorIdx pureReturn rec recOn «break» «continue»)
end Omega.DoResultSBC
namespace Omega.Empty
export _root_.Empty (elim)
end Omega.Empty
namespace Omega.Eq
export _root_.Eq (comm mp mpr ndrecOn substr to_iff)
end Omega.Eq
namespace Omega.Equivalence
export _root_.Equivalence (casesOn mk rec recOn refl symm trans)
end Omega.Equivalence
namespace Omega.Exists
export _root_.Exists (casesOn elim intro rec recOn)
end Omega.Exists
namespace Omega.ForIn
export _root_.ForIn (casesOn forIn mk rec recOn)
end Omega.ForIn
namespace Omega.ForIn'
export _root_.ForIn' (casesOn forIn' mk rec recOn)
end Omega.ForIn'
namespace Omega.ForInStep
export _root_.ForInStep (casesOn ctorElim ctorElimType ctorIdx done rec recOn yield)
end Omega.ForInStep
namespace Omega.Function
export _root_.Function (comp_apply comp_const comp_def comp_id const_apply const_comp false_comp id_comp true_comp)
end Omega.Function
namespace Omega.HEq
export _root_.HEq (comm ndrec ndrecOn subst symm trans)
end Omega.HEq
namespace Omega.HasEquiv
export _root_.HasEquiv (Equiv casesOn mk rec recOn)
end Omega.HasEquiv
namespace Omega.Iff
export _root_.Iff (casesOn comm elim intro mp mpr of_eq rec recOn refl rfl symm trans)
end Omega.Iff
namespace Omega.LawfulBEq
export _root_.LawfulBEq (casesOn eq_of_beq mk rec recOn toReflBEq)
end Omega.LawfulBEq
namespace Omega.Lean
export _root_.Lean (injEq_helper opaqueId)
end Omega.Lean
namespace Omega.Nat
export _root_.Nat (add_zero)
end Omega.Nat
namespace Omega.NonScalar
export _root_.NonScalar (casesOn mk rec recOn val)
end Omega.NonScalar
namespace Omega.Or
export _root_.Or (comm symm)
end Omega.Or
namespace Omega.PEmpty
export _root_.PEmpty (elim)
end Omega.PEmpty
namespace Omega.PNonScalar
export _root_.PNonScalar (casesOn mk rec recOn)
end Omega.PNonScalar
namespace Omega.PSigma
export _root_.PSigma (casesOn fst mk noConfusion noConfusionType rec recOn snd)
end Omega.PSigma
namespace Omega.PSum
export _root_.PSum (casesOn ctorElim ctorElimType ctorIdx inhabitedLeft inhabitedRight inl inr rec recOn)
end Omega.PSum
namespace Omega.PUnit
export _root_.PUnit (eq_punit ext subsingleton)
end Omega.PUnit
namespace Omega.Prod
export _root_.Prod (lexLt lexLtDec map)
end Omega.Prod
namespace Omega.ReflBEq
export _root_.ReflBEq (casesOn mk rec recOn rfl)
end Omega.ReflBEq
namespace Omega.Setoid
export _root_.Setoid (casesOn iseqv mk r rec recOn refl symm trans trivial)
end Omega.Setoid
namespace Omega.Sigma
export _root_.Sigma (casesOn fst mk noConfusion noConfusionType rec recOn snd)
end Omega.Sigma
namespace Omega.Subsingleton
export _root_.Subsingleton (allEq casesOn elim intro rec recOn)
end Omega.Subsingleton
namespace Omega.Subtype
export _root_.Subtype (instBEq instDecidableEq)
end Omega.Subtype
namespace Omega.Sum
export _root_.Sum (casesOn ctorElim ctorElimType ctorIdx inhabitedLeft inhabitedRight inl inr noConfusion noConfusionType nonemptyLeft nonemptyRight rec recOn)
end Omega.Sum
namespace Omega.Thunk
export _root_.Thunk (bind casesOn fn fnImpl fn_eq_fnImpl get map mk pure rec recOn)
end Omega.Thunk
namespace Omega.imp
export _root_.imp (swap)
end Omega.imp
