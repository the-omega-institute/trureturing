import D5.S3.HilbertOperators.CommonAnchorOrderReflection
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w

namespace Reg.D5.S3.HilbertOperators.CommonAnchorOrderReflection
open _root_.D5.S3.HilbertOperators.CommonAnchorOrderReflection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ContinuousLinearMap
open scoped BigOperators InnerProductSpace

local instance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] : CompleteSpace H := FiniteDimensional.complete ℂ H

structure Carrier where
  H : Type v
  [additive : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [finite : FiniteDimensional ℂ H]

abbrev signature : Signature where
  Params := Carrier.{v}
  State p := by
    letI := p.additive
    letI := p.inner
    exact p.H →L[ℂ] p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := by
    letI := p.additive
    letI := p.inner
    exact p.H →L[ℂ] p.H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => by
    letI := p.additive
    letI := p.inner
    exact -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law R := ∀ {E : Type u} {F : Type v} {S : Type w}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [Fintype S] [Nonempty S]
    (V : S → E →L[ℂ] F) (p : S → ℝ) (hp : ∀ l, 0 < p l)
    (hsum : ∑ l, p l = 1) (e : E) (he : e ≠ 0)
    (v : F) (hanchor : ∀ l, V l e = v),
    (ReflectsPSD V p ↔ RankOneTests V p) ∧
    (RankOneTests V p ↔ HasDecoder V) ∧
    (HasDecoder V ↔ Compatible V) ∧
    (∀ (C : F →L[ℂ] E), (∀ l, C.comp (V l) = 1) →
      ∀ X : E →L[ℂ] E, C.comp ((sandwich V p X).comp C.adjoint) = X) ∧
    (∀ X : E →L[ℂ] E, X.IsPositive →
      (R.readout () (@Carrier.mk F inferInstance inferInstance inferInstance)
        (sandwich V p X)).IsPositive)

private theorem actual_law : arena.{u,v,w}.Law actual :=
  @common_anchor_order_reflection

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let E := EuclideanSpace ℂ (ULift.{u} Unit)
  let F := EuclideanSpace ℂ (ULift.{v} Unit)
  let S := ULift.{w} Unit
  let e : E := EuclideanSpace.single ⟨()⟩ 1
  let f : F := EuclideanSpace.single ⟨()⟩ 1
  have he : e ≠ 0 := by
    intro hz
    have ht := congrArg (fun x : E => x ⟨()⟩) hz
    simpa [e] using ht
  have hf : f ≠ 0 := by
    intro hz
    have ht := congrArg (fun x : F => x ⟨()⟩) hz
    simpa [f] using ht
  have hh := h (fun _ : S => (0 : E →L[ℂ] F)) (fun _ => 1)
    (by intro _; norm_num) (by simp) e he 0 (by intro _; rfl)
  have hn := (hh.2.2.2.2 0 isPositive_zero).re_inner_nonneg_left f
  change 0 ≤ (inner ℂ ((-1 : F →L[ℂ] F) f) f).re at hn
  simp only [neg_apply, one_apply, inner_neg_left, Complex.neg_re,
    inner_self_eq_norm_sq] at hn
  have hp := sq_pos_of_pos (norm_pos_iff.mpr hf)
  linarith

def familyRegistration : Registration arena.{u,v,w} (type_of% (@common_anchor_order_reflection.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let F := EuclideanSpace ℂ (ULift.{v} Unit)
    let f : F := EuclideanSpace.single ⟨()⟩ 1
    have hf : f ≠ 0 := by
      intro hz
      have ht := congrArg (fun x : F => x ⟨()⟩) hz
      simpa [f] using ht
    refine ⟨@Carrier.mk F inferInstance inferInstance inferInstance, 0, 1, ?_⟩
    intro hz
    have hh := congrArg (fun X : F →L[ℂ] F => X f) hz
    exact hf (by simpa [actual, realize] using hh.symm)

/-- Typed four-slot attempt; exact raw occurrence binding remains unpaid. -/
def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@common_anchor_order_reflection.{u,v,w})
      (type_of% (realize signature.{v} (fun _ _ X => X) (fun e => nomatch e)))
      Unit Unit where
  unitName := `Reg.D5.S3.HilbertOperators.CommonAnchorOrderReflection.unit
  realizationName := `Reg.D5.S3.HilbertOperators.CommonAnchorOrderReflection.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
end Reg.D5.S3.HilbertOperators.CommonAnchorOrderReflection
