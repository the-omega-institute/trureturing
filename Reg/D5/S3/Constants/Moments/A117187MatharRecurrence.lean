import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Constants.Moments.A117187MatharRecurrence
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Constants.Moments.A117187MatharRecurrence
open _root_.D5.S3.Constants.Moments.A117187MatharRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def changed : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (constantCoeff source_root = 1 ∧ source_root ^ 2 = 1 - 4 * X ^ 2 ∧
      ∀ r : PowerSeries ℤ, constantCoeff r = 1 → r ^ 2 = 1 - 4 * X ^ 2 →
        r = source_root) ∧
    (IsUnit denominator ∧ denominator * invOfUnit denominator 1 = 1 ∧
      invOfUnit denominator 1 * denominator = 1) ∧
    source_series = (1 + X) *
      expand 2 (by decide) D5.S3.Constants.Moments.A331474HankelBridge.F0 ∧
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℤ) + 4) * (31 * n - 12) * R.readout () () n +
      (37 * (n : ℤ) ^ 2 + 24 * n - 156) * R.readout () () (n - 1) -
      4 * (31 * (n : ℤ) ^ 2 + 81 * n + 24) * R.readout () () (n - 2) -
      4 * (37 * (n : ℤ) + 24) * (n - 1) * R.readout () () (n - 3) = 0

private theorem changed_law : ¬ arena.Law changed := by
  intro h
  have hh := h.2.2.2 3 (by decide)
  have ha := result.2.2.2 3 (by decide)
  norm_num [changed, realize] at hh
  norm_num at ha
  linear_combination hh - ha

private theorem initial_values : a 0 = 1 ∧ a 2 = 4 := by
  let T := expand 2 (by decide)
    _root_.D5.S3.Constants.Moments.A331474HankelBridge.F0
  have he (m : ℕ) : coeff (2 * m) T =
      _root_.D5.S3.Constants.Moments.A331474HankelBridge.b m := by
    rw [coeff_expand_mul]
    exact _root_.D5.S3.Constants.Moments.A331474HankelBridge.source_moments.1 m
  have h0 : coeff 0 T = 1 := by
    simpa [_root_.D5.S3.Constants.Moments.A331474HankelBridge.b] using he 0
  have h2 : coeff 2 T = 4 := by
    norm_num [_root_.D5.S3.Constants.Moments.A331474HankelBridge.b] at *
    exact he 1
  have h1 : coeff 1 T = 0 := coeff_expand_of_not_dvd 2 (by decide) _ (by decide)
  have ha (n : ℕ) : a n = coeff n T + coeff n (X * T) := by
    rw [a, result.2.2.1, add_mul, one_mul, map_add]
  constructor
  · rw [ha, h0]
    simp
  · rw [ha, h2]
    have hx : coeff 2 (X * T) = coeff 1 T := by
      simpa using coeff_X_pow_mul T 1 1
    rw [hx, h1]
    norm_num

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, changed, changed_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual changed changed_law
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change a 0 ≠ a 2
    rw [initial_values.1, initial_values.2]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Constants.Moments.A117187MatharRecurrence.auditUnit
  realizationName := `Reg.D5.S3.Constants.Moments.A117187MatharRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Constants.Moments.A117187MatharRecurrence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Constants.Moments.A117187MatharRecurrence
