/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full-tail and cofinal-window tests at fourth powers characterize RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualLinearPeak
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Set
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

lemma remainder_chord {a b x B : ℝ} (ha : 0 < a) (hab : a < b)
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

/-- The quadratic remainder of a chord clipped to one fourth - power cell. -/
lemma quartic_chord_error {n a z : ℝ} (hn : 1 ≤ n)
    (ha : n ^ 4 ≤ a) (haz : a ≤ z) (hz : z ≤ (n + 1) ^ 4) :
    (z - a) ^ 2 / a ≤ 225 * n ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hgap : (n + 1) ^ 4 - n ^ 4 ≤ 15 * n ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sq_nonneg n),
      mul_nonneg (sub_nonneg.mpr hn) hn0.le]
  have hstep := (sub_le_sub hz ha).trans hgap
  apply (div_le_iff₀ ((pow_pos hn0 4).trans_le ha)).mpr
  calc
    _ ≤ (15 * n ^ 3) ^ 2 := pow_le_pow_left₀ (sub_nonneg.mpr haz) hstep _
    _ = 225 * n ^ 2 * n ^ 4 := by ring
    _ ≤ 225 * n ^ 2 * a := mul_le_mul_of_nonneg_left ha (by positivity)

private lemma quartic_cell {n x : ℝ} (hn : 1 ≤ n) (hax : n^4 ≤ x) (hxb : x ≤ (n+1)^4)
    (ha : U (n^4) < n^2) (hb : U ((n+1)^4) < (n+1)^2) : U x ≤ 229*n^2 := by
  have hn0 : 0 < n := by linarith
  have hlt : n^4 < (n+1)^4 := by gcongr; linarith
  have herr := quartic_chord_error hn le_rfl hlt.le le_rfl
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

open Real

/-- Window endpoints and the natural fourth powers between them. -/
def WindowSample (Y Z t : ℝ) : Prop :=
  t ∈ Icc Y Z ∧ (t = Y ∨ t = Z ∨ ∃ n : ℕ, t = (n:ℝ) ^ 4)

/-- A power bound at the two ends and the fourth powers inside the interval
controls the complete Mangoldt remainder at every intermediate real scale. -/
private theorem interpolate_window {Y Z x p : ℝ} (hY : 1 ≤ Y) (hx : x ∈ Icc Y Z)
    (hp : 1 / 2 ≤ p) (hp' : p ≤ 1) (H : ∀ t, WindowSample Y Z t → U t ≤ t ^ p) :
    U x ≤ 241 * x ^ p := by
  have hx1 := hY.trans hx.1
  have hx0 : 0 < x := by linarith
  let y := Real.exp (Real.log x / 4)
  let n : ℕ := ⌊y⌋₊
  let v : ℝ := n
  have hy : 1 ≤ y := Real.one_le_exp (div_nonneg (log_nonneg hx1) (by norm_num))
  have hv : 1 ≤ v := by
    have : 1 ≤ n := Nat.le_floor (by simpa using hy)
    change (1:ℝ) ≤ (n:ℝ)
    exact_mod_cast this
  have hv0 : 0 < v := by linarith
  have hy4 : y ^ 4 = x := by
    rw [show y ^ 4 = exp (4 * (log x / 4)) by exact (exp_nat_mul _ 4).symm]
    rw [show 4 * (log x / 4) = log x by ring, exp_log hx0]
  have hlow : v ^ 4 ≤ x := by
    rw [← hy4]
    exact pow_le_pow_left₀ hv0.le (Nat.floor_le (zero_le_one.trans hy)) _
  have hhigh : x ≤ (v + 1) ^ 4 := by
    rw [← hy4]
    exact pow_le_pow_left₀ (zero_le_one.trans hy) (Nat.lt_floor_add_one y).le _
  let a := max Y (v ^ 4)
  let z := min Z ((v + 1) ^ 4)
  have hax : a ≤ x := max_le hx.1 hlow
  have hxz : x ≤ z := le_min hx.2 hhigh
  have haz := hax.trans hxz
  have ha0 : 0 < a := (zero_lt_one.trans_le hY).trans_le (le_max_left _ _)
  have sa : WindowSample Y Z a := by
    refine ⟨⟨le_max_left _ _, hax.trans hx.2⟩, ?_⟩
    rcases le_total (v ^ 4) Y with h|h
    · exact Or.inl (max_eq_left h)
    · exact Or.inr (Or.inr ⟨n, max_eq_right h⟩)
  have sz : WindowSample Y Z z := by
    refine ⟨⟨hx.1.trans hxz, min_le_left _ _⟩, ?_⟩
    rcases le_total Z ((v + 1) ^ 4) with h|h
    · exact Or.inr (Or.inl (min_eq_left h))
    · exact Or.inr (Or.inr ⟨n + 1, by simpa [z,v] using min_eq_right h⟩)
  have hp0 : 0 ≤ p := by linarith
  have hxp : 0 ≤ x ^ p := rpow_nonneg hx0.le _
  have endpoint {t : ℝ} (ht : WindowSample Y Z t) (htop : t ≤ (v + 1) ^ 4) : U t ≤ 16 * x ^ p := by
    have hstep : (v + 1) ^ 4 ≤ 16 * x := calc
      (v + 1) ^ 4 ≤ (2 * v) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = 16 * v ^ 4 := by ring
      _ ≤ 16 * x := by linarith
    have t0 := (zero_le_one.trans hY).trans ht.1.1
    calc
      U t ≤ t ^ p := H t ht
      _ ≤ (16 * x) ^ p := rpow_le_rpow t0 (htop.trans hstep) hp0
      _ = (16:ℝ) ^ p * x ^ p := mul_rpow (by norm_num) hx0.le
      _ ≤ 16 * x ^ p := by
        gcongr
        simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤16) hp'
  have hUa := endpoint sa (hax.trans hhigh)
  have hUz := endpoint sz (min_le_right _ _)
  rcases haz.eq_or_lt with he|hlt
  · have : a=x := le_antisymm hax (hxz.trans he.ge)
    linarith [this ▸ hUa]
  have herr := quartic_chord_error hv (le_max_right Y (v ^ 4)) haz (min_le_right Z ((v + 1) ^ 4))
  have hs : v ^ 2 ≤ sqrt x := by
    apply (le_sqrt (by positivity) hx0.le).2
    nlinarith only [hlow]
  rw [sqrt_eq_rpow] at hs
  have hxpow := rpow_le_rpow_of_exponent_le hx1 hp
  have hc := remainder_chord ha0 hlt hax hxz hUa hUz
  linarith

/-- On arbitrarily late closed power windows, the two ends and the fourth powers inside
suffice to test the one - sided estimate with every positive exponent loss. -/
theorem rh_iff_quartic_power_windows {b : ℝ} (hb : 1 < b) :
    RiemannHypothesis ↔ ∀ κ : ℝ, 0 < κ → ∃ᶠ Y : ℝ in atTop,
      ∀ t, WindowSample Y (Y ^ b) t → U t ≤ t ^ (1 / 2 + κ) := by
  constructor
  · intro rh κ hκ
    exact ((MangoldtPointwiseWindows.rh_iff_pointwise_power_windows hb).1 rh κ hκ).mono
      (fun Y h t ht => h t ht.1)
  intro hw
  apply (MangoldtPointwiseWindows.rh_iff_pointwise_power_windows hb).2
  intro κ hκ
  let δ := min (κ / 2) (1 / 2)
  have hd : 0 < δ := lt_min (half_pos hκ) (by norm_num)
  have hd1 : 1 / 2 + δ ≤ 1 := by linarith only [min_le_right (κ / 2) (1 / 2:ℝ)]
  have hr : 0 < κ - δ := by linarith only [min_le_left (κ / 2) (1 / 2:ℝ),hκ]
  obtain ⟨T,ht⟩ := eventually_atTop.mp ((tendsto_rpow_atTop hr).eventually_ge_atTop 241)
  apply frequently_atTop.mpr
  intro R
  obtain ⟨Y, H, hY⟩ := ((hw δ hd).and_eventually (eventually_ge_atTop (max (max R T) 2))).exists
  have hR := (le_max_left R T).trans ((le_max_left _ _).trans hY)
  have h2 := (le_max_right _ _).trans hY
  refine ⟨Y, hR, ?_⟩
  intro x hx
  have hx0 : 0<x := by linarith only [h2.trans hx.1]
  have h := interpolate_window (x:=x) (by linarith only [h2]) hx (by linarith only [hd])
    hd1 H
  calc
    _ ≤ 241 * x ^ (1 / 2 + δ) := h
    _ ≤ x ^ (κ - δ) * x ^ (1 / 2 + δ) :=
      mul_le_mul_of_nonneg_right
        (ht x ((le_max_right _ _).trans ((le_max_left _ _).trans (hY.trans hx.1))))
        (rpow_nonneg hx0.le _)
    _ = x ^ (1 / 2 + κ) := by rw [←rpow_add hx0]; congr 1; ring

/-- With fourth powers at both endpoints, every window sample has an integer root
in the corresponding closed interval. -/
private theorem sample_root_of_quartic_ends {a b : ℕ} (hab : a ≤ b) {x : ℝ}
    (hx : WindowSample ((a : ℝ) ^ 4) ((b : ℝ) ^ 4) x) :
    ∃ n : ℕ, a ≤ n ∧ n ≤ b ∧ x = (n : ℝ) ^ 4 := by
  obtain ⟨⟨hlo, hhi⟩, rfl | rfl | ⟨n, rfl⟩⟩ := hx
  · exact ⟨a, le_rfl, hab, rfl⟩
  · exact ⟨b, hab, le_rfl, rfl⟩
  · have lo : a ^ 4 ≤ n ^ 4 := by exact_mod_cast hlo
    have hi : n ^ 4 ≤ b ^ 4 := by exact_mod_cast hhi
    exact ⟨n, le_of_pow_le_pow_left₀ (by decide) (Nat.zero_le _) lo,
      le_of_pow_le_pow_left₀ (by decide) (Nat.zero_le _) hi, rfl⟩

/-- RH is equivalent to testing the one-sided power bound on arbitrarily late
finite integer blocks, at the fourth powers of all roots from k³ through k⁴. -/
theorem rh_iff_quartic_integer_blocks :
    RiemannHypothesis ↔ ∀ κ : ℝ, 0 < κ → ∀ A : ℕ, ∃ k ≥ max A 2,
      ∀ n : ℕ, k ^ 3 ≤ n → n ≤ k ^ 4 → U ((n : ℝ) ^ 4) ≤ ((n : ℝ) ^ 4) ^ (1 / 2 + κ) := by
  constructor
  · intro rh κ hκ A
    obtain ⟨N, hN⟩ := eventually_atTop.mp (rh_iff_eventually_quartic_samples.mp rh)
    let k := max (max A 2) N
    have hk : max A 2 ≤ k := le_max_left _ _
    have hk1 : 1 ≤ k := by omega
    refine ⟨k, hk, ?_⟩
    intro n hlo _
    have hkn : k ≤ n := (le_self_pow₀ hk1 (by decide : 3 ≠ 0)).trans hlo
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hk1.trans hkn
    have hn := hN n ((le_max_right (max A 2) N).trans hkn)
    have hsqrt : ((n : ℝ) ^ 4) ^ (1 / 2 : ℝ) = (n : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast (n : ℝ) 4, ← Real.rpow_mul (by positivity)]
      norm_num
    exact hn.le.trans (hsqrt ▸ Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ hn1) (by linarith only [hκ] : (1 / 2 : ℝ) ≤ 1 / 2 + κ))
  · intro blocks
    apply (rh_iff_quartic_power_windows (b := (4 : ℝ) / 3) (by norm_num)).mpr
    intro κ hκ
    apply frequently_atTop.mpr
    intro R
    obtain ⟨k, hk, hblock⟩ := blocks κ hκ ⌈R⌉₊
    have hk1 : 1 ≤ k := by omega
    have hkR : R ≤ (k : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (le_max_left ⌈R⌉₊ 2).trans hk)
    have hY : (k : ℝ) ≤ (k : ℝ) ^ 12 :=
      le_self_pow₀ (by exact_mod_cast hk1) (by decide)
    refine ⟨(k : ℝ) ^ 12, hkR.trans hY, ?_⟩
    have hZ : ((k : ℝ) ^ 12) ^ ((4 : ℝ) / 3) = (k : ℝ) ^ 16 := by
      rw [← Real.rpow_natCast (k : ℝ) 12, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hZ]
    intro x hx
    have hends : WindowSample (((k ^ 3 : ℕ) : ℝ) ^ 4) (((k ^ 4 : ℕ) : ℝ) ^ 4) x := by
      convert hx using 1 <;> push_cast <;> ring
    obtain ⟨n, hlo, hhi, rfl⟩ := sample_root_of_quartic_ends
      (pow_le_pow_right₀ hk1 (by decide : 3 ≤ 4)) hends
    exact hblock n hlo hhi

end D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling
