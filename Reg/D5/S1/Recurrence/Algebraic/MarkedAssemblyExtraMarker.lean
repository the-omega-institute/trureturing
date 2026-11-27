import D5.S1.Recurrence.Algebraic.MarkedAssemblyExtraMarker
import D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The exponential of the strict prefix at the endpoint as a dependent readout. -/

namespace Reg.D5.S1.Recurrence.Algebraic.MarkedAssemblyExtraMarker

open _root_.D5.S1.Recurrence.Algebraic.MarkedAssemblyExtraMarker
open _root_.D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients (prefixSeries)
open _root_.D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality (expSeries_coeff)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ)
    (fun _ => ℕ → ℤ) (fun _ => PowerSeries ℚ)

def actual : Realization signature :=
  realize signature
    (fun _ param a => (exp ℚ).subst (C ((param.2 : ℚ) ^ param.1) * prefixSeries param.2 a))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => C (1 / 2 : ℚ) * X) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d N : ℕ) (a : ℕ → ℤ), 1 ≤ N → ∀ p : ℕ, p.Prime → ¬p ∣ N →
    (∀ f : ℕ, 1 ≤ f → f < N →
      let H := (exp ℚ).subst (C ((f : ℚ) ^ d) * prefixSeries N a)
      coeff f H = (f : ℚ) ^ (d + 1) * coeff (f - 1) H) →
    let H := R.readout () ⟨d, N⟩ a
    0 ≤ padicValRat p (coeff N H - (N : ℚ) ^ (d + 1) * coeff (N - 1) H)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 1 (fun _ => 0) le_rfl 2 (by decide) (by norm_num) (by omega)
  change 0 ≤ padicValRat 2
    (coeff 1 (C (1 / 2 : ℚ) * X) - (↑(1 : ℕ) : ℚ) ^ (0 + 1) *
      coeff (1 - 1) (C (1 / 2 : ℚ) * X)) at hb
  have hv : padicValRat 2 (1 / 2 : ℚ) = -1 := by
    let : Fact (Nat.Prime 2) := ⟨by decide⟩
    rw [padicValRat.div (by norm_num) (by norm_num), padicValRat.one,
      show padicValRat 2 (2 : ℚ) = 1 from padicValRat.self (by decide)]
    norm_num
  norm_num [coeff_C_mul, coeff_zero_eq_constantCoeff, hv] at hb

private theorem first_coeff (a : ℕ → ℤ) :
    coeff 1 (actual.readout () ⟨0, 2⟩ a) = (a 1 : ℚ) := by
  change coeff 1 ((exp ℚ).subst (C ((2 : ℚ) ^ 0) * prefixSeries 2 a)) = _
  simp only [pow_zero, map_one, one_mul]
  rw [expSeries_coeff _ (by simp [prefixSeries])]
  simp [Finset.sum_range_succ, prefixSeries]

def family : Registration arena (type_of% signed_prefix_residual_local_integral) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨signed_prefix_residual_local_integral, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨0, 2⟩, fun _ => 0, fun _ => 1, ?_⟩
    intro h
    have hc := congrArg (coeff 1) h
    rw [Subsingleton.elim i ()] at hc
    simp only [first_coeff, Int.cast_zero, Int.cast_one, zero_ne_one] at hc

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    signed_prefix_residual_local_integral (Realization signature) Unit Unit where
  unitName :=
    `D5.S1.Recurrence.Algebraic.MarkedAssemblyExtraMarker.signed_prefix_residual_local_integral.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.MarkedAssemblyExtraMarker.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ param a => (exp ℚ).subst (C ((param.2 : ℚ) ^ param.1) * prefixSeries param.2 a))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.MarkedAssemblyExtraMarker
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Recurrence.Algebraic.MarkedAssemblyExtraMarker
