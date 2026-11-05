import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Completion.RawAnchoredFourierQuotient

/-! Full-telescope source registration of the retained C133-V prerequisite. -/

namespace Reg.D5.S3.Quantum.Completion.RawAnchoredFourierQuotient
open _root_.D5.S3.Quantum.Completion.ThreePhaseHistoryRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {M : Type u} [MulOneClass M]
    (U : M → M) (u : M) (N : Set M), (1 : M) ∈ N →
    (∀ x ∈ N, ∀ k : ZMod 3, x * U^[k.val] u ∈ N) →
    ∀ (χ : AddChar (ZMod 3) ℂ), Function.Injective χ →
    ∀ (f D : M → ℂ) (C : ℝ),
    (∀ x ∈ N, Complex.normSq (f x) ≤ C) →
    (∀ x ∈ N, ∀ k : ZMod 3,
      f (x * U^[k.val] u) = f x + χ k * f u + χ⁻¹ k * D x) →
    R.readout () () (f u) 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (M := ULift.{u} Unit) id 1 Set.univ (Set.mem_univ _)
    (fun _ _ _ => Set.mem_univ _) ZMod.stdAddChar ZMod.injective_stdAddChar
    (fun _ => 0) (fun _ => 0) 0 (fun _ _ => by simp)
    (fun _ _ _ => by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  intro he
  have hbad : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena.{u} (type_of% @bounded_phase_recursion_vanishes.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bounded_phase_recursion_vanishes.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bounded_phase_recursion_vanishes.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.ThreePhaseHistoryRigidity.bounded_phase_recursion_vanishes.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawAnchoredFourierQuotient.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Completion.RawAnchoredFourierQuotient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Completion.RawAnchoredFourierQuotient
