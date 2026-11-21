/- GID: D5/S3/CharacterSums/NonprincipalCharacterGrowth
   generality: G
   mirror-B: D5/B/S3/CharacterSums/NonprincipalCharacterGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonprincipal Dirichlet L-functions on the right half-plane satisfy a half-totient growth bound. -/

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
/-! # Growth of nonprincipal Dirichlet L-functions

A complementary pair of sums in one period controls the Mellin integral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory Finset Complex Asymptotics
namespace D5.S3.CharacterSums.NonprincipalCharacterGrowth

private theorem char_prefix {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Icc 1 n, χ (k:ZMod q)‖ ≤ (q.totient:ℝ)/2 := by
  classical
  have complete {E : Type} [AddCommMonoid E] (f : ZMod q → E) :
      ∑ k ∈ range q, f (k:ZMod q) = ∑ z : ZMod q, f z := by
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      _ = ∑ k : Fin q, f (ZMod.finEquiv q k) := by
        apply sum_congr rfl
        intro k _
        congr 1
        cases q with
        | zero => exact Fin.elim0 k
        | succ q => exact Fin.cast_val_eq_self k
      _ = _ := (ZMod.finEquiv q).sum_comp f
  have block : ∑ k ∈ range q, χ (k:ZMod q) = 0 :=
    (complete χ).trans (MulChar.sum_eq_zero_of_ne_one hne)
  have mass : ∑ k ∈ range q, ‖χ (k:ZMod q)‖ = (q.totient:ℝ) := by
    rw [complete (fun z => ‖χ z‖)]
    have val (z : ZMod q) : ‖χ z‖ = (1 : DirichletCharacter ℝ q) z := by
      by_cases h : IsUnit z
      · exact (χ.unit_norm_eq_one h.unit).trans (MulChar.one_apply_coe h.unit).symm
      · rw [χ.map_nonunit h, norm_zero, MulChar.map_nonunit _ h]
    simp_rw [val]
    rw [MulChar.sum_one_eq_card_units,ZMod.card_units_eq_totient]
  have blocks (m : ℕ) : ∑ k ∈ range (q*m), χ (k:ZMod q) = 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ,sum_range_add,ih,zero_add]
      simpa using block
  have bound (m : ℕ) : ‖∑ k ∈ range m, χ (k:ZMod q)‖ ≤ (q.totient:ℝ)/2 := by
    nth_rw 1 [show m=q*(m/q)+m%q from (Nat.div_add_mod m q).symm]
    rw [sum_range_add,blocks,zero_add]
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add]
    have hsub : range (m%q) ⊆ range q := range_mono (Nat.mod_lt m (NeZero.pos q)).le
    have total := sum_sdiff hsub (f:=fun k : ℕ => χ (k:ZMod q))
    rw [block,add_eq_zero_iff_eq_neg] at total
    have rest := norm_sum_le (range q \ range (m%q)) (fun k : ℕ => χ (k:ZMod q))
    rw [total,norm_neg] at rest
    have initial := norm_sum_le (range (m%q)) (fun k : ℕ => χ (k:ZMod q))
    have split := sum_sdiff hsub (f:=fun k : ℕ => ‖χ (k:ZMod q)‖)
    rw [mass] at split
    linarith only [initial,rest,split]
  have qne : q≠1 := by rintro rfl;exact hne (DirichletCharacter.level_one χ)
  have ident : range (n+1) = insert 0 (Finset.Icc 1 n) := by ext k;simp;omega
  have h := bound (n+1)
  rwa [ident,sum_insert (by simp),Nat.cast_zero,χ.map_zero' qne,zero_add] at h


private def characterSum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k:ZMod q)

private theorem growth_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    {s : ℂ} (hs : 0<s.re) : χ.LFunction s =
      s * ∫ t in Set.Ioi (1:ℝ), characterSum χ t*(t:ℂ)^(-(s+1)) := by
  let A := (Set.Ioi (1:ℝ)).indicator (characterSum χ)
  let G (w : ℂ) := w*mellin A (-w)
  let U := {w : ℂ | 0<w.re}
  have op : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have pre : IsPreconnected U := (convex_halfSpace_gt (Complex.reCLM.isLinear) (0:ℝ)).isPreconnected
  have bA (t : ℝ) : ‖A t‖ ≤ (q.totient:ℝ)/2 := by
    by_cases h : t ∈ Set.Ioi (1:ℝ)
    · simpa [A,Set.indicator_of_mem h,characterSum] using char_prefix χ hne ⌊t⌋₊
    · simp only [A, Set.indicator_of_notMem h, norm_zero]; positivity
  have meas : Measurable A := by
    apply Measurable.indicator _ measurableSet_Ioi
    exact (measurable_of_countable (f:=fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k:ZMod q))).comp Nat.measurable_floor
  have loc : LocallyIntegrableOn A (Ioi 0) :=
    (locallyIntegrableOn_const ((q.totient:ℝ)/2) (s:=Ioi (0:ℝ))).mono meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => by simpa using bA t))
  have top : A =O[atTop] (fun t : ℝ => t^(-(0:ℝ))) := by
    apply Asymptotics.IsBigO.of_bound ((q.totient:ℝ)/2)
    exact Filter.Eventually.of_forall (fun t => by simpa using bA t)
  have dg (w : ℂ) (hw : w ∈ U) : DifferentiableAt ℂ G w := by
    have bot : A =O[𝓝[>] (0:ℝ)] (fun t : ℝ => t^(-(-w.re-1))) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))] with t ht
      have ht1 : t ∉ Set.Ioi (1:ℝ) := not_lt.mpr ht.le
      simp [A,Set.indicator_of_notMem ht1]
    have hm := mellin_differentiableAt_of_isBigO_rpow (s:= -w) loc top
      (by simpa [U] using hw) bot (by simp)
    exact differentiableAt_id.mul (hm.comp w (differentiableAt_id.neg))
  have repr (w : ℂ) : G w = w * ∫ t in Ioi (1:ℝ), characterSum χ t*(t:ℂ)^(-(w+1)) := by
    change w*(∫ t in Ioi (0:ℝ), (t:ℂ)^(-w-1) • (Ioi (1:ℝ)).indicator (characterSum χ) t) = _
    congr 1
    have eqi (t : ℝ) : (t:ℂ)^(-w-1) • (Ioi (1:ℝ)).indicator (characterSum χ) t =
        (Ioi (1:ℝ)).indicator (fun t : ℝ => (t:ℂ)^(-w-1) • characterSum χ t) t := by
      by_cases h : t ∈ Set.Ioi (1:ℝ) <;> simp [h]
    simp_rw [eqi]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi,Set.Ioi_inter_Ioi,max_eq_right (by norm_num : (0:ℝ)≤1)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change (t:ℂ)^(-w-1)*characterSum χ t = characterSum χ t*(t:ℂ)^(-(w+1))
    rw [show -w-1 = -(w+1) by ring, mul_comm]
  have right (w : ℂ) (hw : 1<w.re) : χ.LFunction w = G w := by
    rw [repr,χ.LFunction_eq_LSeries hw]
    apply LSeries_eq_mul_integral (fun n : ℕ => χ (n:ZMod q)) (r:=0) le_rfl (by linarith)
      ((χ.LSeriesSummable_iff (NeZero.ne q)).mpr hw)
    apply Asymptotics.IsBigO.of_bound ((q.totient:ℝ)/2)
    exact Filter.Eventually.of_forall (fun n => by simpa using char_prefix χ hne n)
  have near : χ.LFunction =ᶠ[𝓝 (2:ℂ)] G := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (show (1:ℝ)<(2:ℂ).re by norm_num)] with w hw
    exact right w hw
  have hdG : DifferentiableOn ℂ G U := fun w hw => (dg w hw).differentiableWithinAt
  have eqG := ((χ.differentiable_LFunction hne).differentiableOn.analyticOnNhd op).eqOn_of_preconnected_of_eventuallyEq
    (hdG.analyticOnNhd op) pre
    (show (2:ℂ) ∈ U by change 0<(2:ℂ).re;norm_num) near
  exact (eqG hs).trans (repr s)



/-- Pairing each incomplete period with its complement bounds the growth of a
nonprincipal character on the entire right half-plane by half the unit mass. -/
theorem nonprincipal_growth {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ (q.totient:ℝ)/2 * ‖s‖ / s.re := by
  have ha : -(s.re+1) < -1 := by linarith
  have hc : (0:ℝ)<1 := zero_lt_one
  have bound : ‖∫ t in Set.Ioi (1:ℝ), characterSum χ t*(t:ℂ)^(-(s+1))‖ ≤ ((q.totient:ℝ)/2)/s.re := by
    refine (norm_integral_le_integral_norm _).trans ?_
    calc
      _ ≤ ∫ t in Set.Ioi (1:ℝ), ((q.totient:ℝ)/2)*t^(-(s.re+1)) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          ((integrableOn_Ioi_rpow_of_lt ha hc).const_mul ((q.totient:ℝ)/2))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 := hc.trans (Set.mem_Ioi.mp ht)
        rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [neg_re, add_re, one_re]
        exact mul_le_mul_of_nonneg_right (char_prefix χ hne _) (Real.rpow_nonneg ht0.le _)
      _ = _ := by
        rw [integral_const_mul,integral_Ioi_rpow_of_lt ha hc,Real.one_rpow]
        rw [show -(s.re+1)+1 = -s.re by ring]
        ring
  rw [growth_integral χ hne hs,norm_mul]
  calc
    _ ≤ ‖s‖ * (((q.totient:ℝ)/2)/s.re) := mul_le_mul_of_nonneg_left bound (norm_nonneg s)
    _ = _ := by ring

end D5.S3.CharacterSums.NonprincipalCharacterGrowth
