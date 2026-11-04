import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the sharp lower bound for skewness plus kurtosis. -/

namespace Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound

open _root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound
open _root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum (skewness)
open _root_.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound (kurtosis)
open _root_.D5.S3.Quantum.Transport.StrongAbsorption.Foundations (powerSum)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe skewness plus kurtosis for every cycle size and rate vector. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => skewness k + kurtosis k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => lowerBound) (fun e => nomatch e)

/-- Retain both the universal strict inequality and the complete greatest-lower-bound clause. -/
abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ n : ℕ, 2 ≤ n → ∀ k : Fin n → ℝ, (∀ i, 0 < k i) →
      lowerBound < r.readout () n k) ∧
    IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
      (∀ i, 0 < k i) ∧ s = skewness k + kurtosis k} lowerBound

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.1 2 (by norm_num) (fun _ => 1) (fun _ => by norm_num)
  change lowerBound < lowerBound at hbad
  exact lt_irrefl _ hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  change skewness (fun _ : Fin 1 => (0 : ℝ)) + kurtosis (fun _ : Fin 1 => (0 : ℝ)) ≠
    skewness (fun _ : Fin 1 => (1 : ℝ)) + kurtosis (fun _ : Fin 1 => (1 : ℝ))
  norm_num [skewness, kurtosis, powerSum]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.source_registration
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
    (realize signature (fun _ _ k => skewness k + kurtosis k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound
    definition := some {
      owner := `D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound
      name := `D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.result
#print _root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound
