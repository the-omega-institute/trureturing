import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
import Reg.Support.DependentFamily

/-! Source-bound audit of the sharp minimum of unicyclic current skewness. -/

namespace Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum

open _root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the sharp minimum as the number of cycle states varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => minimumValue n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain attainment and the universal lower bound over all positive rate vectors. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 2 ≤ n →
    IsLeast {s : ℝ | ∃ k : Fin n → ℝ, (∀ i, 0 < k i) ∧ s = skewness k}
      (r.readout () () n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hvalue := (result 2 (by norm_num)).unique (h 2 (by norm_num))
  change minimumValue 2 = 0 at hvalue
  norm_num [minimumValue] at hvalue

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  change minimumValue 2 ≠ minimumValue 3
  norm_num [minimumValue]

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
      (@_root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.source_registration
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
    (realize signature (fun _ _ n => minimumValue n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
    definition := some {
      owner := `D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
      name := `D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

namespace Normalized

open _root_.D5.S3.Quantum.Transport.StrongAbsorption.Foundations (powerSum)

/-- Observe the inverse-rate power sum used to normalize every coordinate. -/
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
  realize signature (fun _ n k => powerSum n 1 (fun j => (k j)⁻¹))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the normalization identity over the complete original rate domain. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (k : Fin n → ℝ),
    skewness k = simplexFunctional (fun i => (k i)⁻¹ / r.readout () n k)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (n := 1) (fun _ => 1)
  norm_num [rejected, realize, skewness, simplexFunctional, powerSum] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, powerSum]

def source_registration : Registration arena
    (∀ {n : ℕ} (k : Fin n → ℝ),
      skewness k = simplexFunctional
        (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@skewness_normalized, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness_normalized)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.Normalized.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.Normalized.source_registration
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
    (realize signature (fun _ n k => powerSum n 1 (fun j => (k j)⁻¹))
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness_normalized
#print _root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.simplexFunctional
#print axioms source_registration
#print axioms registration

end Normalized


namespace NormalizedSimplex

open _root_.D5.S3.Quantum.Transport.StrongAbsorption.Foundations (powerSum)

-- The source theorem uses the set-valued `stdSimplex` interface.
set_option linter.deprecated false

/-- Observe the inverse-rate power sum appearing in the normalized simplex vector. -/
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
  realize signature (fun _ n k => powerSum n 1 (fun j => (k j)⁻¹))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain simplex membership for every nonempty positive rate vector. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ}, 0 < n → ∀ k : Fin n → ℝ, (∀ i, 0 < k i) →
    (fun i => (k i)⁻¹ / r.readout () n k) ∈ stdSimplex ℝ (Fin n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (n := 1) (by norm_num) (fun _ => 1) (fun _ => by norm_num)
  norm_num [rejected, realize, stdSimplex] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, powerSum]

def source_registration : Registration arena
    (∀ {n : ℕ}, 0 < n → ∀ k : Fin n → ℝ, (∀ i, 0 < k i) →
      (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) ∈
        stdSimplex ℝ (Fin n)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_simplex, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.normalized_simplex)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.NormalizedSimplex.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.NormalizedSimplex.source_registration
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
    (realize signature (fun _ n k => powerSum n 1 (fun j => (k j)⁻¹))
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.normalized_simplex
#print axioms source_registration
#print axioms registration

end NormalizedSimplex

end
end Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
