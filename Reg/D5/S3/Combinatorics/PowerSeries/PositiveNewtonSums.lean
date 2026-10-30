import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.PowerSeries

noncomputable section

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ+
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ k => positiveCoefficient k) (fun e => nomatch e)

def series (R : DependentFamily.Realization signature) : ℚ⟦X⟧ :=
  mk fun n => R.readout () () ⟨n + 1, by omega⟩

def denominator : ℚ⟦X⟧ := (1 - X) * (2 - (1 + X) ^ 5)
def numerator : ℚ⟦X⟧ := 1 - X * (1 + X) ^ 4

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => series R * denominator = numerator ∧ recurrence (R.readout () ())

abbrev sourceScope := type_of% (@result)

lemma denominator_constant : constantCoeff denominator ≠ 0 := by
  norm_num [denominator, map_ofNat]

lemma source_bridge : sourceScope ↔ arena.Law actual := by
  change (positiveSeries = numerator * denominator⁻¹ ∧ recurrence positiveCoefficient) ↔
    (positiveSeries * denominator = numerator ∧ recurrence positiveCoefficient)
  exact and_congr (eq_mul_inv_iff_mul_eq denominator_constant) Iff.rfl

lemma actual_positive : arena.Law actual := source_bridge.mp result

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : ℚ)) (fun e => nomatch e)

lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := congrArg (constantCoeff (R := ℚ)) h.1
  norm_num [series, rejected, DependentFamily.realize, numerator] at h0

lemma dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1 : ℕ+), (2 : ℕ+), ?_⟩
  intro he
  change positiveCoefficient 1 = positiveCoefficient 2 at he
  have hd : denominator = 1 - 6 * X - 5 * X ^ 2 + 5 * X ^ 4 + 4 * X ^ 5 + X ^ 6 := by
    unfold denominator; ring
  have h0 := congrArg (coeff 0) actual_positive.1
  have h1 := congrArg (coeff 1) actual_positive.1
  have hx : (X : ℚ⟦X⟧) = X ^ 1 := by simp
  rw [hd] at h0 h1
  simp only [mul_add, mul_sub, mul_one, mul_comm (series actual), mul_assoc] at h0 h1
  rw [hx] at h0 h1
  simp only [← pow_mul, Nat.one_mul] at h0 h1
  norm_num [map_add, map_sub, coeff_ofNat_mul, coeff_mul_ofNat, coeff_X_pow_mul',
    coeff_mul_X_pow', series, actual, DependentFamily.realize, numerator, coeff_mul,
    Finset.Nat.antidiagonal_succ] at h0 h1
  norm_num only [PNat.val_ofNat] at he
  linarith

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (by cases j; cases i; rfl)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@result) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ _ k => positiveCoefficient k) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some ℕ+
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums
    definition := some {
      owner := `D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums
      name := `D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums.recurrence
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end

end Reg.D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums
