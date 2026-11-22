import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuEndpointQuarticPrefix

/-! Source binding for the quartic comparison on all four endpoint prefixes. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuRankOneEndpointFloor

namespace Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticPrefix

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def equalityOnly : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (Eq.mp (congrFun h 0) (le_refl 0))

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : Fin 4 → ℝ), Antitone x → (∀ i, 0 ≤ x i) → ∀ k : Fin 4,
    R.readout () () (spectralMoment 1 x ^ 2 * (spectralMoment 2 x - spectralMoment 1 x ^ 2) ^ 2 / 5)
      (spectralMoment 3 x * spectralMoment 3 (endpointPrefixAverage k (endpointClassical x)) -
        spectralMoment 2 x * spectralMoment 4 (endpointPrefixAverage k (endpointClassical x)))

private def stepSpectrum (i : Fin 4) : ℝ := if i < 2 then 1 else 0

private theorem stepSpectrum_antitone : Antitone stepSpectrum := by
  intro i j hij
  by_cases hj : j < 2
  · simp [stepSpectrum, hj, hij.trans_lt hj]
  · simp only [stepSpectrum, ite_eq_right hj]
    split <;> norm_num

private theorem stepSpectrum_nonneg (i : Fin 4) : 0 ≤ stepSpectrum i := by
  unfold stepSpectrum
  split <;> norm_num

private theorem stepSpectrum_moment {k : ℕ} (hk : k ≠ 0) :
    spectralMoment k stepSpectrum = 1 / 2 := by
  simp only [spectralMoment, Fin.sum_univ_four, stepSpectrum]
  norm_num [zero_pow hk]

private theorem endpoint_stepSpectrum :
    endpointPrefixAverage 3 (endpointClassical stepSpectrum) =
      ![endpointAlpha, endpointAlpha, endpointBeta, endpointBeta] := by
  funext i
  fin_cases i <;>
    norm_num [endpointPrefixAverage, endpointClassical, stepSpectrum, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    first
    | linear_combination endpointAlpha * endpointAlpha_add_beta
    | linear_combination endpointBeta * endpointAlpha_add_beta

private theorem stepSpectrum_output_gap :
    spectralMoment 3 stepSpectrum *
        spectralMoment 3 (endpointPrefixAverage 3 (endpointClassical stepSpectrum)) -
      spectralMoment 2 stepSpectrum *
        spectralMoment 4 (endpointPrefixAverage 3 (endpointClassical stepSpectrum)) =
      5 / 288 := by
  have hProduct : endpointAlpha * endpointBeta = (1 / 12 : ℝ) := by
    unfold endpointAlpha endpointBeta
    linear_combination -(1 / 4 : ℝ) * lambda_sq
  have hSquares : endpointAlpha ^ 2 + endpointBeta ^ 2 = (5 / 6 : ℝ) := by
    unfold endpointAlpha endpointBeta
    linear_combination (1 / 2 : ℝ) * lambda_sq
  rw [stepSpectrum_moment (by decide : 3 ≠ 0), stepSpectrum_moment (by decide : 2 ≠ 0),
    endpoint_stepSpectrum]
  simp only [spectralMoment, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  calc
    _ = endpointAlpha * endpointBeta * (endpointAlpha ^ 2 + endpointBeta ^ 2) / 4 := by
      linear_combination -(endpointAlpha ^ 3 + endpointBeta ^ 3) / 4 * endpointAlpha_add_beta
    _ = _ := by rw [hProduct, hSquares]; norm_num

private theorem equalityOnly_fails : ¬ arena.Law equalityOnly := by
  intro h
  have he := h stepSpectrum stepSpectrum_antitone stepSpectrum_nonneg 3
  change _ = _ at he
  rw [stepSpectrum_output_gap, stepSpectrum_moment (by decide : 1 ≠ 0),
    stepSpectrum_moment (by decide : 2 ≠ 0)] at he
  norm_num at he

def family : Registration arena (type_of% @endpoint_quartic_prefix) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpoint_quartic_prefix, equalityOnly, equalityOnly_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual equalityOnly equalityOnly_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_quartic_prefix) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuEndpointQuarticPrefix.endpoint_quartic_prefix.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticPrefix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuEndpointQuarticPrefix
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Semigroups.WuEndpointQuarticPrefix
