import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth
import Reg.Support.SingleDependentReadout

/-! Complete source-family observation of the normalized ordered-word average. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth

open LeanInformationAudit
open _root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℕ) (fun _ => Row) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p v => average p.1 p.2 v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ρ : ℝ) (_hρ : 0 < ρ) (_hρ₁ : ρ < 1) (k : ℕ) (v : Row),
    0 < growthFactor ρ ∧ growthFactor ρ < Real.sqrt (1 + 3 * ρ ^ 2) ∧
      Real.sqrt (1 + 3 * ρ ^ 2) < 2 ∧ 1 < growthFactor ρ ∧
      R.readout () ⟨ρ, k⟩ v ≤ growthFactor ρ ^ k * ‖v‖

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (1/2) (by norm_num) (by norm_num) 0 0).2.2.2.2
  norm_num [rejected, realize] at hh

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1/2, 0⟩, 0, WithLp.toLp 2 ![1, 0], ?_⟩
  change average (1/2) 0 0 ≠ average (1/2) 0 (WithLp.toLp 2 ![1, 0])
  simp [average, word, rowAction, EuclideanSpace.norm_eq, Fin.sum_univ_two]

def family : Registration arena (type_of% (@annealed_growth)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@annealed_growth, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@annealed_growth) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => average p.1 p.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms annealed_growth
#print axioms registration

end Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth
