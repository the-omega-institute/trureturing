import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the strict unicyclic kurtosis bound and its sharp infimum. -/

namespace Reg.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound

open _root_.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound
open _root_.D5.S3.Quantum.Transport.StrongAbsorption.Foundations (powerSum)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe kurtosis for every cycle size and every rate vector. -/
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
  realize signature (fun _ _ k => kurtosis k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => lowerBound) (fun e => nomatch e)

/-- Retain both the universal strict inequality and the complete greatest-lower-bound clause. -/
abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ n : ℕ, 2 ≤ n → ∀ k : Fin n → ℝ, (∀ i, 0 < k i) →
      lowerBound < r.readout () n k) ∧
    IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
      (∀ i, 0 < k i) ∧ s = kurtosis k} lowerBound

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.1 2 (by norm_num) (fun _ => 1) (fun _ => by norm_num)
  change lowerBound < lowerBound at hbad
  exact lt_irrefl _ hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  change kurtosis (fun _ : Fin 1 => (0 : ℝ)) ≠ kurtosis (fun _ : Fin 1 => (1 : ℝ))
  norm_num [kurtosis, powerSum]

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
      (@_root_.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.source_registration
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
    (realize signature (fun _ _ k => kurtosis k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound
    definition := some {
      owner := `D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound
      name := `D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.claim
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

#print _root_.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.result
#print _root_.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.claim
#print axioms source_registration
#print axioms registration

#print _root_.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.normalized
#print _root_.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.moments

namespace Normalized

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
  realize signature
    (fun _ n k => powerSum n 3 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Vary the normalized cubic moment in the complete normalization identity. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (k : Fin n → ℝ),
    kurtosis k =
      15 * powerSum n 2 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) ^ 2 -
      20 * r.readout () n k +
      6 * powerSum n 4 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) /
        powerSum n 2 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (n := 1) (fun _ => 1)
  norm_num [rejected, realize, kurtosis, powerSum] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, powerSum]

def source_registration : Registration arena
    (∀ {n : ℕ} (k : Fin n → ℝ),
      kurtosis k =
        15 * powerSum n 2 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) ^ 2 -
        20 * powerSum n 3 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) +
        6 * powerSum n 4 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) /
          powerSum n 2 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.normalized)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.Normalized.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.Normalized.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n k => powerSum n 3 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Normalized

namespace Moments

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
  realize signature (fun _ n x => powerSum n 2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Vary the quadratic moment in the complete conjunction of moment inequalities. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ}, 2 ≤ n → ∀ x : Fin n → ℝ, (∀ i, 0 < x i) →
    0 < r.readout () n x ∧ 0 ≤ powerSum n 3 x ∧
      powerSum n 3 x ^ 2 ≤ powerSum n 2 x * powerSum n 4 x ∧
      powerSum n 4 x < powerSum n 2 x ^ 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (n := 2) (by norm_num) (fun _ => 1) (fun _ => by norm_num)).1
  exact lt_irrefl (0 : ℝ) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, powerSum]

def source_registration : Registration arena
    (∀ {n : ℕ}, 2 ≤ n → ∀ x : Fin n → ℝ, (∀ i, 0 < x i) →
      0 < powerSum n 2 x ∧ 0 ≤ powerSum n 3 x ∧
        powerSum n 3 x ^ 2 ≤ powerSum n 2 x * powerSum n 4 x ∧
        powerSum n 4 x < powerSum n 2 x ^ 2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moments, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.moments)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.Moments.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.Moments.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n x => powerSum n 2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Moments

end
end Reg.D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound
