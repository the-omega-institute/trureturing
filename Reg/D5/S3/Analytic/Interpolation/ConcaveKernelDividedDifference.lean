import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference
import Reg.Support.SingleDependentReadout

open Set MeasureTheory LeanInformationAudit
open _root_.D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Interval

namespace Reg.D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference

noncomputable section

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ value bound => value < bound) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have heq := congrFun h 1
  have h01 : (0 : ℝ) < 1 := zero_lt_one
  have h11 : (1 : ℝ) < 1 := Eq.mp heq h01
  exact (lt_irrefl _) h11

abbrev integralArena : Arena where
  signature := signature
  Law R := ∀ {left right a b c : ℝ} {h k : ℝ → ℝ},
    left < right → a < b → b < c → c ≤ right →
    ContinuousOn h (Icc (min a left) right) → ContinuousOn k (Icc left right) →
    ConcaveOn ℝ (Icc left right) k →
    (∀ t ∈ Icc left right, 0 ≤ k t) → (∀ t ∈ Ioo left right, 0 < k t) →
    (∀ t ∈ Ioo left right \ Icc a b, h t < 0) →
    ((∫ t in a..b, max (h t) 0) < ∫ t in b..c, -h t * ((c - t) / (c - a))) →
    R.readout () () (∫ t in left..right, h t * k t) 0

private theorem constant_negative_lobe_bound :
    (∫ _ : ℝ in (-2 : ℝ)..(-1), max (-1 : ℝ) 0) <
      ∫ t in (-1 : ℝ)..1, -(-1 : ℝ) * ((1 - t) / (1 - (-2))) := by
  simp only [max_eq_right (show (-1 : ℝ) ≤ 0 by norm_num), intervalIntegral.integral_zero,
    neg_neg, one_mul]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (((continuous_const.sub continuous_id).div_const _).intervalIntegrable _ _)
  · intro t ht
    exact div_pos (sub_pos.mpr ht.2) (by norm_num)
  · norm_num

private theorem integral_rejected : ¬ integralArena.Law rejected := by
  intro h
  exact h (left := 0) (right := 2) (a := -2) (b := -1) (c := 1)
    (h := fun _ => -1) (k := fun _ => 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    continuousOn_const continuousOn_const (concaveOn_const _ (convex_Icc _ _))
    (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)
    constant_negative_lobe_bound

def integralFamily : Registration integralArena (type_of% @integral_mul_concave_neg_of_lobe_bound)
    where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_mul_concave_neg_of_lobe_bound, rejected, integral_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    integralArena.Law actual rejected integral_rejected
  dependence := dependence

def integralAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_mul_concave_neg_of_lobe_bound) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference.integral_mul_concave_neg_of_lobe_bound
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference.integralFamily
  realizationSource := none
  generated := false
  arena := .source ⟨integralArena⟩
  objectArena := .source ⟨integralArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integralArena ⟨integralFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference
    definition := none
    coordinates := #[]
    readouts := #[{
      path := (List.replicate 18 "body" ++ ["fn", "fn"]).toArray
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev differenceArena : Arena where
  signature := signature
  Law R := ∀ {left mid right a b c : ℝ} {f fp fpp : ℝ → ℝ},
    left < mid → mid < right → a < b → b < c → c ≤ right →
    (∀ t ∈ Icc left right, HasDerivAt f (fp t) t) →
    (∀ t ∈ Icc left right, HasDerivAt fp (fpp t) t) →
    ContinuousOn fpp (Icc (min a left) right) →
    (∀ t ∈ Ioo left right \ Icc a b, fpp t < 0) →
    ((∫ t in a..b, max (fpp t) 0) < ∫ t in b..c, -fpp t * ((c - t) / (c - a))) →
    R.readout () () ((f right - f mid) / (right - mid)) ((f mid - f left) / (mid - left))

private theorem difference_rejected : ¬ differenceArena.Law rejected := by
  intro h
  exact h (left := 0) (mid := 1) (right := 2) (a := -2) (b := -1) (c := 1)
    (f := fun t => -(t * t) / 2) (fp := fun t => -t) (fpp := fun _ => -1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun t _ => by
      convert (((hasDerivAt_id' t).fun_mul (hasDerivAt_id' t)).fun_neg.div_const 2) using 1
      ring)
    (fun t _ => (hasDerivAt_id' t).fun_neg)
    continuousOn_const (by intros; norm_num) constant_negative_lobe_bound

def differenceFamily :
    Registration differenceArena (type_of% @three_node_slope_sub_slope_neg_of_lobe_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@three_node_slope_sub_slope_neg_of_lobe_bound, rejected, difference_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    differenceArena.Law actual rejected difference_rejected
  dependence := dependence

def differenceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@three_node_slope_sub_slope_neg_of_lobe_bound) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference.three_node_slope_sub_slope_neg_of_lobe_bound
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference.differenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨differenceArena⟩
  objectArena := .source ⟨differenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source differenceArena ⟨differenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference
    definition := none
    coordinates := #[]
    readouts := #[{
      path := (List.replicate 19 "body" ++ ["fn", "fn"]).toArray
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.Interpolation.ConcaveKernelDividedDifference
