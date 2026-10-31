import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint
import Reg.Support.DependentFamily

/-! Source-bound audit of cardinality after flipping an absent coordinate. -/

namespace Reg.D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint

open _root_.D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the original set's cardinality in its original dimension. -/
abbrev signature : Signature where
  Params := ℕ
  State d := Finset (Fin d)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ σ => σ.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain every dimension, set, coordinate, and nonmembership hypothesis. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (σ : Finset (Fin d)) (k : Fin d), k ∉ σ →
    (symmDiff σ {k}).card = R.readout () d σ + 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (∅ : Finset (Fin 1)) 0 (by simp)
  norm_num [rejected, realize] at hbad
  have hcard := flip_card_not_mem (∅ : Finset (Fin 1)) 0 (by simp)
  simp only [Finset.card_empty] at hcard
  omega

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, ∅, {0}, ?_⟩
  change (∅ : Finset (Fin 1)).card ≠ ({0} : Finset (Fin 1)).card
  simp

def source_registration : Registration arena
    (∀ {d : ℕ} (σ : Finset (Fin d)) (k : Fin d), k ∉ σ →
      (symmDiff σ {k}).card = σ.card + 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨flip_card_not_mem, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint.flip_card_not_mem)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ σ => σ.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint.flip_card_not_mem
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint
