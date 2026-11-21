/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: RH is equivalent to a one-sided square-root bound at all sufficiently large fourth powers. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualLinearPeak
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling

private lemma mangoldt_chord {a b x p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : p + q = 1)
    (hc : p * a + q * b = x) :
    mangoldtPart x ≤ p * mangoldtPart a + q * mangoldtPart b := by
  have hsum := ((mangoldtPart_summable ha).mul_left p).add ((mangoldtPart_summable hb).mul_left q)
  calc
    mangoldtPart x ≤ ∑' n : ℕ, (p * mangoldtRamp n a + q * mangoldtRamp n b) := by
      apply (mangoldtPart_summable hx).tsum_le_tsum _ hsum
      intro n
      unfold mangoldtRamp
      let s (z : ℝ) := z / (n : ℝ) - 1
      have heq : s x = p * s a + q * s b := by
        dsimp [s]
        rw [← hc]
        ring_nf
        linarith
      have hm : max (s x) 0 ≤ p * max (s a) 0 + q * max (s b) 0 := by
        apply max_le
        · rw [heq]
          gcongr <;> exact le_max_left _ _
        · positivity
      calc
        _ ≤ ArithmeticFunction.vonMangoldt n * (p * max (s a) 0 + q * max (s b) 0) :=
          mul_le_mul_of_nonneg_left hm ArithmeticFunction.vonMangoldt_nonneg
        _ = _ := by dsimp [s]; ring
    _ = p * mangoldtPart a + q * mangoldtPart b := by
      rw [Summable.tsum_add ((mangoldtPart_summable ha).mul_left p)
        ((mangoldtPart_summable hb).mul_left q), tsum_mul_left, tsum_mul_left, mangoldtPart, mangoldtPart]

private lemma log_tangent_bounds {a z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    0 ≤ z * Real.log z - z * Real.log a - (z - a) ∧
    z * Real.log z - z * Real.log a - (z - a) ≤ (z - a)^2 / a := by
  have hlo := Real.one_sub_inv_le_log_of_pos (div_pos hz ha)
  have hhi := Real.log_le_sub_one_of_pos (div_pos hz ha)
  rw [Real.log_div hz.ne' ha.ne', inv_div] at hlo
  rw [Real.log_div hz.ne' ha.ne'] at hhi
  constructor
  · have := mul_le_mul_of_nonneg_left hlo hz.le
    field_simp [hz.ne'] at this
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hhi hz.le
    apply (le_div_iff₀ ha).mpr
    have h' := mul_le_mul_of_nonneg_right h ha.le
    field_simp [ha.ne'] at h'
    nlinarith

private lemma remainder_chord {a b x B : ℝ} (ha : 0 < a) (hab : a < b)
    (hax : a ≤ x) (hxb : x ≤ b) (hau : U a ≤ B) (hbu : U b ≤ B) :
    U x ≤ B + (b-a)^2/a := by
  let q := (x-a)/(b-a)
  let p := 1-q
  have hba : 0 < b-a := sub_pos.mpr hab
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr hax) hba.le
  have hq1 : q ≤ 1 := (div_le_one hba).mpr (by linarith)
  have hp : 0 ≤ p := sub_nonneg.mpr hq1
  have hs : p + q = 1 := by dsimp [p]; ring
  have hmul : q * (b-a) = x-a := div_mul_cancel₀ _ hba.ne'
  have hc : p * a + q * b = x := by dsimp [p]; linarith only [hmul]
  have hr := mangoldt_chord ha.le (ha.trans hab).le (ha.trans_le hax).le hp hq hs hc
  rw [U_eq_complete_ramps ha.le] at hau
  rw [U_eq_complete_ramps (ha.trans hab).le] at hbu
  rw [U_eq_complete_ramps (ha.trans_le hax).le]
  have hl := (log_tangent_bounds ha (ha.trans_le hax)).1
  have hu := mul_le_mul_of_nonneg_left (log_tangent_bounds ha (ha.trans hab)).2 hq
  have hm := mul_le_mul_of_nonneg_right hq1 (div_nonneg (sq_nonneg (b-a)) ha.le)
  have hw := add_le_add (mul_le_mul_of_nonneg_left hau hp) (mul_le_mul_of_nonneg_left hbu hq)
  have hlinear (c : ℝ) : p * (c*a) + q * (c*b) = c*x := by rw [← hc]; ring
  nlinarith only [hr, hl, hu, hm, hw, hlinear (1+Real.eulerMascheroniConstant),
    hlinear (Real.log a), hc, congrArg (fun z : ℝ => z*B) hs, congrArg (fun z : ℝ => z*a) hs]

private lemma quartic_cell {n x : ℝ} (hn : 1 ≤ n) (hax : n^4 ≤ x) (hxb : x ≤ (n+1)^4)
    (ha : U (n^4) < n^2) (hb : U ((n+1)^4) < (n+1)^2) : U x ≤ 229*n^2 := by
  have hn0 : 0 < n := by linarith
  have hgap : (n+1)^4-n^4 ≤ 15*n^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sq_nonneg n),
      mul_nonneg (sub_nonneg.mpr hn) hn0.le]
  have hlt : n^4 < (n+1)^4 := by gcongr; linarith
  have herr : ((n+1)^4-n^4)^2 / n^4 ≤ 225*n^2 := by
    apply (div_le_iff₀ (pow_pos hn0 4)).mpr
    calc
      _ ≤ (15*n^3)^2 := by gcongr
      _ = _ := by ring
  have hend : (n+1)^2 ≤ 4*n^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hn) hn0.le]
  have h := remainder_chord (pow_pos hn0 4) hlt hax hxb (ha.le.trans (by nlinarith [sq_nonneg n])) (hb.le.trans hend)
  linarith

private lemma quartic_bound_of_rh (hRH : RiemannHypothesis) :
    ∀ᶠ n : ℕ in atTop, U ((n : ℝ)^4) < (n : ℝ)^2 := by
  have he := (RHSharpActualEnvelope.actual_G_control hRH).1 (1-firstLiMass)
    (sub_pos.mpr firstLiMass_lt_one)
  have hlim : Tendsto (fun n : ℕ => 4 * Real.log (n : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  filter_upwards [hlim.eventually he, eventually_ge_atTop (1 : ℕ)] with n h hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have h4 : Real.exp (4 * Real.log (n : ℝ)) = (n : ℝ)^4 := by
    simpa [Real.exp_log hn0] using Real.exp_nat_mul (Real.log (n : ℝ)) 4
  have h2 : Real.exp (-(4 * Real.log (n : ℝ))/2) = ((n : ℝ)^2)⁻¹ := by
    rw [show -(4 * Real.log (n : ℝ))/2 = -(2 * Real.log (n : ℝ)) by ring, Real.exp_neg]
    congr 1
    simpa [Real.exp_log hn0] using Real.exp_nat_mul (Real.log (n : ℝ)) 2
  change |Real.exp (-(4 * Real.log (n : ℝ))/2) * U (Real.exp (4 * Real.log (n : ℝ)))| < _ at h
  rw [h4,h2] at h
  have hlt : U ((n : ℝ)^4) / (n : ℝ)^2 < 1 := by
    rw [div_eq_inv_mul]
    linarith [(le_abs_self (((n : ℝ)^2)⁻¹ * U ((n : ℝ)^4)))]
  simpa using (div_lt_one (pow_pos hn0 2)).mp hlt

/-- A strict one-sided test only at fourth powers characterizes RH. -/
theorem rh_iff_eventually_quartic_samples :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, U ((n : ℝ)^4) < (n : ℝ)^2 := by
  refine ⟨quartic_bound_of_rh, ?_⟩
  intro hs
  obtain ⟨N, hN⟩ := eventually_atTop.1 hs
  let T := 4 * Real.log (max (N : ℝ) 1) + 1
  have hT : 0 < T := by dsimp [T]; linarith [Real.log_nonneg (le_max_right (N : ℝ) 1)]
  apply actual_kernel_affine_tail_implies_rh T 0 230 hT
  intro t ht
  let y := Real.exp (t / 4)
  have ht0 : 0 < t := hT.trans_le ht
  have hy : max (N : ℝ) 1 ≤ y := by
    rw [← Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (le_max_right _ _))]
    dsimp [T] at ht
    linarith
  let n := ⌊y⌋₊
  have hnN : N ≤ n := Nat.le_floor ((le_max_left _ _).trans hy)
  have hn1 : 1 ≤ n := Nat.le_floor (by simpa using (le_max_right _ _).trans hy)
  have hleft := Nat.floor_le (Real.exp_nonneg (t/4))
  have hright := Nat.lt_floor_add_one y
  have h4 : y^4 = Real.exp t := by
    dsimp [y]
    rw [← Real.exp_nat_mul]
    congr 1; norm_num; ring
  have h2 : y^2 = Real.exp (t/2) := by
    dsimp [y]
    rw [← Real.exp_nat_mul]
    congr 1; norm_num; ring
  have hquad := quartic_cell (n := (n : ℝ)) (x := y^4) (by exact_mod_cast hn1)
    (by gcongr) (by gcongr) (hN n hnN)
    (by simpa [Nat.cast_add] using hN (n+1) (by omega))
  have hnle : (n : ℝ) ≤ y := hleft
  have hsquare : (n : ℝ)^2 ≤ y^2 := by gcongr
  rw [h4] at hquad
  rw [h2] at hsquare
  have htriv := trivialT_le_mass ht0.le
  have hlog : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK : U (Real.exp t) - Real.log (2*Real.pi) + trivialT t ≤ 229*Real.exp (t/2) + 1 := by linarith
  rw [ActualKernelLocalPositivity.K, abs_of_pos ht0, zero_mul, zero_add]
  calc
    _ ≤ Real.exp (-t/2) * (229*Real.exp (t/2) + 1) :=
      mul_le_mul_of_nonneg_left hK (Real.exp_nonneg _)
    _ = 229 + Real.exp (-t/2) := by
      have hprod : Real.exp (-t/2) * Real.exp (t/2) = 1 := by
        rw [← Real.exp_add, show -t/2+t/2=0 by ring, Real.exp_zero]
      nlinarith only [hprod]
    _ ≤ 230 := by linarith [Real.exp_le_one_iff.mpr (show -t/2 ≤ 0 by linarith)]

end D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling
