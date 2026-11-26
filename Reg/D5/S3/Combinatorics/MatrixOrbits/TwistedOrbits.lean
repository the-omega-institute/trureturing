import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.MatrixOrbits.SymmetricRepresentativeSeries
import Reg.Support.UniverseSingleReadout

/-! Observations of the twisted orbit counts and the four row sums. -/

namespace Reg.D5.S3.Combinatorics.MatrixOrbits.TwistedOrbits

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.A333886
open LeanInformationAudit PowerSeries

noncomputable section

open scoped BigOperators

namespace CycleMultiplicity

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Fin 5) (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ _ k => cycleMultiplicity k) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    (∑ k : Fin 5, R.readout () () k * Nat.card (TwistMat (rep k) n)) = 24 * a333886 n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  simp only [rejected, realize, zero_mul, Finset.sum_const_zero] at he
  have hz := source_identity_literal 0
  rw [coeff_zero_eq_constantCoeff_apply] at hz
  have hc : constantCoeff publishedSeries = 1 := by
    simp [publishedSeries, publishedNumerator, constantCoeff_invOfUnit]
  change (Nat.card (sourceClasses 0) : ℚ) = constantCoeff publishedSeries at hz
  rw [hc, ← Nat.card_congr (sourceClassesEquiv 0)] at hz
  change (a333886 0 : ℚ) = 1 at hz
  have hcard : a333886 0 = 1 := by exact_mod_cast hz
  simp [hcard] at he

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  cases role
  decide

def family : Registration arena (type_of% @cycle_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cycle_count, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cycle_count) (Realization signature) Unit Unit where
  unitName := `A333886.cycle_count.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => cycleMultiplicity k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.TwistedOrbits
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CycleMultiplicity

namespace FirstRow

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature (Σ p : P, Σ k : ℕ, TwistPattern p k) (fun q => Fin q.2.1 → ℕ) (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ q v => ∑ j : I, v (q.2.2.label 0 j)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : P} {k n : ℕ} (pat : TwistPattern p k) (v : Fin k → ℕ),
    pat.rows n v ↔ R.readout () ⟨p, k, pat⟩ v = n ∧
      (∑ j : I, v (pat.label 1 j)) = n ∧
      (∑ j : I, v (pat.label 2 j)) = n ∧
      (∑ j : I, v (pat.label 3 j)) = n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr : pattern0.rows 0 (fun _ => 0) := by intro i; simp
  have he : (1 : ℕ) = 0 := ((h pattern0 (fun _ => 0)).mp hr).1
  exact Nat.one_ne_zero he

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨rep0, 10, pattern0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change (∑ _ : Fin 4, (0 : ℕ)) ≠ ∑ _ : Fin 4, (1 : ℕ)
  decide

def family : Registration arena (type_of% @four_rows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@four_rows, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@four_rows) (Realization signature) Unit Unit where
  unitName := `A333886.four_rows.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q v => ∑ j : I, v (q.2.2.label 0 j)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.TwistedOrbits
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FirstRow

end
end Reg.D5.S3.Combinatorics.MatrixOrbits.TwistedOrbits
