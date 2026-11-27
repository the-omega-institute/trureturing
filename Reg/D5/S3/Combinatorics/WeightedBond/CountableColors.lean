import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.WeightedBond.CompleteGraphSpecialization
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the countable-color specialization equality. -/

open _root_.D5.S3.Combinatorics.WeightedBond PowerSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.WeightedBond.CountableColors

private theorem factor_two : inverseFactor (R := Mark) 0 = 1 := by
  ext n
  cases n with
  | zero => simp [inverseFactor]
  | succ n => simp [inverseFactor, PowerSeries.coeff_one]

private theorem reciprocal_two (t : Mark) : reciprocalFactor 0 t = 1 := by
  unfold reciprocalFactor
  rw [factor_two, map_one]
  simpa using (mul_invOfUnit (1 : PowerSeries Mark) 1 (by simp))

theorem source_one_two : sourceSpecialization 1 2 = 1 := by
  rw [sourceSpecialization_eq, psiComplete_closed 0 0, reciprocal_two]
  simp

private theorem source_two_two : sourceSpecialization 2 2 = 1 - 2 * Polynomial.X := by
  rw [sourceSpecialization_eq, psiComplete_closed 1 0, reciprocal_two]
  norm_num [coeff_rescale, coeff_exp]

theorem source_dependence : sourceSpecialization 1 2 ≠ sourceSpecialization 2 2 := by
  rw [source_one_two, source_two_two]
  intro h
  have hc := congrArg (fun P : Mark => P.coeff 1) h
  norm_num [Polynomial.coeff_sub, Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Polynomial.coeff_X, Polynomial.coeff_one] at hc

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => Mark)

def actual : Realization signature :=
  realize signature (fun _ r n => sourceSpecialization n r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n r : ℕ, R.readout () r n = psiComplete n r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : (0 : Mark) = psiComplete 1 2 := h 1 2
  rw [← sourceSpecialization_eq, source_one_two] at hzero
  exact zero_ne_one hzero

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨2, 1, 2, source_dependence⟩

def family : Registration arena (type_of% sourceSpecialization_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sourceSpecialization_eq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    sourceSpecialization_eq (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.WeightedBond.CountableColors.specialization
  realizationName := `Reg.D5.S3.Combinatorics.WeightedBond.CountableColors.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r n => sourceSpecialization n r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.WeightedBond.CountableColors
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.WeightedBond.CountableColors
end
