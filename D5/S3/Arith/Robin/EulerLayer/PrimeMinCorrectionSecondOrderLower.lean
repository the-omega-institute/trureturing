/- GID: D5/S3/Arith/Robin/EulerLayer/PrimeMinCorrectionSecondOrderLower
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/EulerLayer/PrimeMinCorrectionSecondOrderLower
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: A uniform three-term lower correction for every initial prime support. -/

import D5.S3.Arith.Robin.PrimeMinCorrectionLower
import D5.S3.Arith.Robin.EulerLayer.EulerLayerRootSecondOrder
import D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative finite prime-min bounds with the original integer clock. -/

namespace D5.S3.Arith.Robin.PrimeMinCorrectionSecondOrderLower

open Finset Filter
open scoped Topology Chebyshev
open EulerLayerRootSecondOrder OriginalEndpointPrimeTail

noncomputable section

/-- The normalized implicit equation gives a uniform quadratic root error. -/
private theorem root_error {h x : ℝ} (hh : 0 ≤ h) (hx : 1 ≤ x)
    (hxs : x ≤ Real.sqrt 2)
    (heq : x ^ 2 * (1 + 2 * h * Real.log x) = 2) :
    |x - Real.sqrt 2| ≤ h ∧
      |x - Real.sqrt 2 + (Real.sqrt 2 * Real.log 2 / 2) * h| ≤ 4 * h ^ 2 := by
  let s := Real.sqrt 2
  let b := Real.log 2
  let u := Real.log x
  let d := s - x
  let q := x ^ 2 / (x + s)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ s := by nlinarith
  have hs15 : s < 3 / 2 := by nlinarith
  have hb0 : 0 ≤ b := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hb1 : b < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    dsimp [b]; linarith
  have hx0 : 0 < x := by linarith
  have hden : 0 < x + s := by positivity
  have hv : Real.log s = b / 2 := Real.log_sqrt (by norm_num)
  have hu0 : 0 ≤ u := Real.log_nonneg hx
  have huv : u ≤ b / 2 := by
    calc
      Real.log x ≤ Real.log s := Real.log_le_log hx0 hxs
      _ = b/2 := hv
  have hd0 : 0 ≤ d := sub_nonneg.mpr hxs
  have hq0 : 0 ≤ q := div_nonneg (sq_nonneg x) hden.le
  have hqx : 2 * q ≤ x := by
    dsimp [q]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hqs : q ≤ s / 2 := by linarith
  have hqdiff : 0 ≤ s / 2 - q ∧ s / 2 - q ≤ d := by
    constructor
    · linarith
    · apply (mul_le_mul_iff_left₀ hden).mp
      have hqq : q*(x+s)=x^2 := div_mul_cancel₀ _ hden.ne'
      change (s/2-q)*(x+s) ≤ (s-x)*(x+s)
      nlinarith only [hqq, hs2, mul_le_mul_of_nonneg_left hxs hs0.le]
  have hugap : 0 ≤ b / 2 - u ∧ b / 2 - u ≤ d := by
    have ht := Real.log_le_sub_one_of_pos (div_pos hs0 hx0)
    rw [Real.log_div hs0.ne' hx0.ne', hv] at ht
    have hgap : b / 2 - u ≤ (s - x) / x := by
      have hid : s/x-1 = (s-x)/x := by field_simp [hx0.ne']
      change b/2-u ≤ s/x-1 at ht
      exact ht.trans_eq hid
    constructor
    · linarith
    · have hdiv : (s - x) / x ≤ s - x := div_le_self hd0 hx
      exact hgap.trans hdiv
  have hdu : d = h * (2 * q * u) := by
    apply (mul_right_cancel₀ hden.ne')
    have hqq : q * (x + s) = x ^ 2 := div_mul_cancel₀ _ hden.ne'
    calc
      d*(x+s) = 2*h*x^2*u := by
        dsimp only [d, u]
        change x^2*(1+2*h*Real.log x)=2 at heq
        nlinarith only [heq, hs2]
      _ = h*(2*(q*(x+s))*u) := by rw [hqq]; ring
      _ = h*(2*q*u)*(x+s) := by ring
  have hfu : 0 ≤ 2 * q * u := by positivity
  have hf1 : 2 * q * u ≤ 1 := by
    calc
      2 * q * u ≤ s * (b / 2) :=
        mul_le_mul (by linarith : 2 * q ≤ s) huv hu0 hs0.le
      _ ≤ 1 := by nlinarith
  have hd : d ≤ h := by rw [hdu]; exact mul_le_of_le_one_right hh hf1
  have hfgap : 0 ≤ s * b / 2 - 2 * q * u ∧
      s * b / 2 - 2 * q * u ≤ 4 * d := by
    have ha := mul_le_mul_of_nonneg_right hqdiff.2 hb0
    have hb := mul_le_mul_of_nonneg_left hugap.2 (by positivity : 0 ≤ 2 * q)
    have hc := mul_le_mul_of_nonneg_right (by linarith : 2 * q ≤ s) hd0
    constructor
    · nlinarith [mul_le_mul (by linarith : 2 * q ≤ s) huv hu0 hs0.le]
    · nlinarith
  constructor
  · rw [abs_of_nonpos (sub_nonpos.mpr hxs)]
    simpa only [d, neg_sub] using hd
  · have hid : x - s + (s * b / 2) * h = h * (s * b / 2 - 2 * q * u) := by
      dsimp [d] at hdu
      linarith
    change |x - s + (s * b / 2) * h| ≤ 4 * h ^ 2
    rw [hid, abs_of_nonneg (mul_nonneg hh hfgap.1)]
    have := mul_le_mul_of_nonneg_left hfgap.2 hh
    nlinarith [mul_le_mul_of_nonneg_left hd hh]

/-- The real root belongs to the finite head, including when it is prime. -/
private theorem finite_root_prime_min_lower {X ρ : ℝ} {P : ℕ}
    (hX : 1 < X) (hρ : 1 < ρ)
    (heq : ρ ^ 2 * Real.log ρ = X * Real.log X) (hP : ρ ≤ (P : ℝ)) :
    θ ρ / (X * Real.log X) +
      (∑ p ∈ (Ioc ⌊ρ⌋₊ P).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      ∑ p ∈ Nat.primesLE P, min (Real.log p / (X * Real.log X))
        (-Real.log (1 - (p : ℝ)⁻¹ ^ 2)) := by
  classical
  let f : ℕ → ℝ := fun p => min (Real.log p / (X * Real.log X))
    (-Real.log (1 - (p : ℝ)⁻¹ ^ 2))
  let H := Nat.primesLE ⌊ρ⌋₊
  let S := Nat.primesLE P
  have hsub : H ⊆ S := Nat.primesLE_mono (Nat.floor_le_of_le hP)
  have hD : 0 < X * Real.log X := mul_pos (by linarith) (Real.log_pos hX)
  have hhead : θ ρ / (X * Real.log X) ≤ ∑ p ∈ H, f p := by
    rw [Chebyshev.theta_eq_sum_primesLE, Finset.sum_div]
    apply sum_le_sum
    intro p hp
    have hpρ : (p : ℝ) ≤ ρ :=
      (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1).trans (Nat.floor_le (by linarith))
    exact PrimeMinCorrectionLower.prime_weight_lower hX hD le_rfl heq.le
      (Nat.mem_primesLE.mp hp).2 hpρ
  have hsets : S \ H = (Ioc ⌊ρ⌋₊ P).filter Nat.Prime := by
    ext p
    constructor
    · intro hp
      have hmem := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, hmem.1⟩, hmem.2⟩
      apply lt_of_not_ge
      intro hle
      exact (Finset.mem_sdiff.mp hp).2 (Nat.mem_primesLE.mpr ⟨hle, hmem.2⟩)
    · intro hp
      have hmem := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
      have hprime := (Finset.mem_filter.mp hp).2
      refine Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hmem.2, hprime⟩, ?_⟩
      intro hbad
      exact not_le_of_gt hmem.1 (Nat.mem_primesLE.mp hbad).1
  have htail : (∑ p ∈ S \ H, (1 : ℝ) / (p : ℝ) ^ 2) ≤ ∑ p ∈ S \ H, f p := by
    apply sum_le_sum
    intro p hp
    have hps := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
    have hph : ⌊ρ⌋₊ < p := by
      have hnot := (mem_sdiff.mp hp).2
      simp only [H, Nat.mem_primesLE, hps.2, and_true] at hnot
      omega
    have hpρ : ρ < (p : ℝ) := (Nat.floor_lt (by linarith : 0 ≤ ρ)).mp hph
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hps.2.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hps.2.one_lt
    have hmono := second_cutoff_strictMono hρ (by simpa using hp1) hpρ
    change ρ^2*Real.log ρ < (p:ℝ)^2*Real.log p at hmono
    rw [heq] at hmono
    have hi : (p : ℝ)⁻¹ ^ 2 < 1 :=
      pow_lt_one₀ (inv_pos.mpr hp0).le ((inv_lt_one₀ hp0).mpr hp1) (by norm_num)
    have ht := Real.log_le_sub_one_of_pos (sub_pos.mpr hi)
    apply le_min
    · apply (div_le_div_iff₀ (sq_pos_of_pos hp0) hD).mpr
      simpa only [one_mul, mul_comm] using hmono.le
    · have hid : (1 : ℝ) / (p : ℝ) ^ 2 = (p : ℝ)⁻¹ ^ 2 := by ring
      rw [hid]
      linarith
  rw [← hsets]
  have hadd := add_le_add hhead htail
  have hsum := sum_sdiff (f := f) hsub
  dsimp only [S] at hsum
  linarith only [hadd, hsum]

private theorem root_normalized {X : ℝ} (hX : 2 ≤ X) :
    let x := second_cutoff_root X / Real.sqrt X
    1 ≤ x ∧ x ≤ Real.sqrt 2 ∧
      x ^ 2 * (1 + 2 * (1 / Real.log X) * Real.log x) = 2 := by
  obtain ⟨hρ1, hlo, hhi, heq⟩ := second_cutoff_root_spec hX
  let x := second_cutoff_root X / Real.sqrt X
  have hX0 : 0 < X := by linarith
  have hr : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hx0 : 0 < x := div_pos (by linarith) hr
  have hρ : second_cutoff_root X = x * Real.sqrt X := by
    dsimp [x]; field_simp
  have hsq : (second_cutoff_root X) ^ 2 = x ^ 2 * X := by
    rw [hρ, mul_pow, Real.sq_sqrt hX0.le]
  have hlog : Real.log (second_cutoff_root X) = Real.log x + Real.log X / 2 := by
    rw [hρ, Real.log_mul hx0.ne' hr.ne', Real.log_sqrt hX0.le]
  have hraw : x ^ 2 * (Real.log x + Real.log X / 2) = Real.log X := by
    rw [hsq, hlog] at heq
    apply mul_left_cancel₀ hX0.ne'
    nlinarith only [heq]
  refine ⟨(le_div_iff₀ hr).mpr (by simpa using hlo.le), ?_, ?_⟩
  · apply (div_le_iff₀ hr).mpr
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hhi
    exact hhi.le
  · change x ^ 2 * (1 + 2 * (1 / Real.log X) * Real.log x) = 2
    field_simp
    nlinarith only [hraw]

private theorem profile_last_lipschitz {x : ℝ} (hx : 1 ≤ x) (hxs : x ≤ Real.sqrt 2) :
    |8 * ((Real.log x)^2 + 2 * Real.log x + 2) / x -
      8 * ((Real.log (Real.sqrt 2))^2 + 2 * Real.log (Real.sqrt 2) + 2) /
        Real.sqrt 2| ≤ 2 * |x - Real.sqrt 2| := by
  let F : ℝ → ℝ := fun t => 8 * ((Real.log t)^2 + 2 * Real.log t + 2) / t
  let F' : ℝ → ℝ := fun t => -8 * (Real.log t)^2 / t^2
  have hs : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hb : Real.log (2 : ℝ) < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 (Real.sqrt 2)) : HasDerivWithinAt F (F' t)
      (Set.Icc 1 (Real.sqrt 2)) t := by
    have ht0 : 0 < t := by linarith [ht.1]
    have hl := Real.hasDerivAt_log ht0.ne'
    have hh := (((hl.pow 2).add (hl.const_mul 2)).add_const 2).const_mul 8
    have hh' := hh.div (hasDerivAt_id t) ht0.ne'
    apply HasDerivAt.hasDerivWithinAt
    convert hh' using 1
    · rfl
    · dsimp [F']
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq]
      field_simp [ht0.ne']
      <;> ring
  have hbnd (t : ℝ) (ht : t ∈ Set.Icc 1 (Real.sqrt 2)) : ‖F' t‖ ≤ 2 := by
    have ht0 : 0 < t := by linarith [ht.1]
    have hu0 : 0 ≤ Real.log t := Real.log_nonneg ht.1
    have hu : Real.log t ≤ 1 / 2 := by
      have := Real.log_le_log ht0 ht.2
      rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at this
      linarith
    rw [Real.norm_eq_abs]
    dsimp [F']
    rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (Real.log t)])
      (sq_nonneg t))]
    rw [← neg_div]
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
    nlinarith [sq_nonneg (Real.log t), sq_nonneg t, ht.1]
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbnd
    (convex_Icc (1 : ℝ) (Real.sqrt 2)) (show Real.sqrt 2 ∈ Set.Icc 1 (Real.sqrt 2) from
      ⟨hs, le_rfl⟩) (show x ∈ Set.Icc 1 (Real.sqrt 2) from ⟨hx, hxs⟩)
  simpa only [Real.norm_eq_abs, F] using hh

set_option maxHeartbeats 800000 in
-- The four rational and stationary-profile remainders are elaborated in one proof term.
private theorem profile_error {h x : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hx : 1 ≤ x) (hxs : x ≤ Real.sqrt 2)
    (heq : x ^ 2 * (1 + 2 * h * Real.log x) = 2) :
    |x + (1 / x) * (2 / (1 + 2 * h * Real.log x) -
        4 * h / (1 + 2 * h * Real.log x)^2 +
        16 * h^2 / (1 + 2 * h * Real.log x)^3) -
      (2 * Real.sqrt 2 - Real.sqrt 2 * (2 + Real.log 2) * h +
        Real.sqrt 2 * (8 + 4 * Real.log 2 + 3 * (Real.log 2)^2 / 4) * h^2)| ≤
      79 * h^3 := by
  let s := Real.sqrt 2
  let b := Real.log 2
  let u := Real.log x
  let δ := x - s
  let a := -s * b / 2
  let z := 2 * h * u
  let F0 := x + 2 / x
  let F1 := -4 * (u + 1) / x
  let F2 := 8 * (u^2 + 2 * u + 2) / x
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : s^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ s := by nlinarith
  have hs15 : s < 3 / 2 := by nlinarith
  have hb0 : 0 ≤ b := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hb1 : b ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    dsimp [b]; linarith
  have hv : Real.log s = b / 2 := Real.log_sqrt (by norm_num)
  have hx0 : 0 < x := by linarith
  have hu0 : 0 ≤ u := Real.log_nonneg hx
  have hu : u ≤ b / 2 := by
    calc
      Real.log x ≤ Real.log s := Real.log_le_log hx0 hxs
      _ = b/2 := hv
  have hz0 : 0 ≤ z := by positivity
  have hzh : z ≤ h := by dsimp [z]; nlinarith
  have hzv : 0 < 1 + z := by positivity
  have hdiv (w : ℝ) : |w / x| ≤ |w| := by
    rw [abs_div, abs_of_pos hx0]
    exact div_le_self (abs_nonneg _) hx
  have hroot := root_error hh0 hx hxs heq
  have hd : |δ| ≤ h := hroot.1
  have hda : |δ - a * h| ≤ 4 * h^2 := by
    simpa only [δ, a, s, b, neg_mul, neg_div, sub_neg_eq_add] using hroot.2
  have ha : |a| ≤ 1 := by
    rw [abs_of_nonpos (show a ≤ 0 by dsimp [a]; nlinarith only [mul_nonneg hs0.le hb0])]
    dsimp [a]
    nlinarith
  have had : |δ + a * h| ≤ 2 * h := by
    calc
      |δ + a * h| ≤ |δ| + |a * h| := abs_add_le _ _
      _ ≤ h + 1 * h := add_le_add hd (by
        rw [abs_mul, abs_of_nonneg hh0]
        exact mul_le_mul_of_nonneg_right ha hh0)
      _ = 2 * h := by ring
  have hf0 : |F0 - (2 * s + (a^2 / s) * h^2)| ≤ 9 * h^3 := by
    have hid : F0 - (2 * s + (a^2 / s) * h^2) =
        (δ - a*h) * (δ + a*h) / x + a^2*h^2*(s-x)/(x*s) := by
      dsimp [F0, δ]
      field_simp [hx0.ne', hs0.ne']
      linear_combination -s*hs2
    have he1 : |(δ - a*h) * (δ + a*h) / x| ≤ 8 * h^3 := by
      apply (hdiv _).trans
      rw [abs_mul]
      have := mul_le_mul hda had (abs_nonneg _) (by positivity : 0 ≤ 4*h^2)
      nlinarith only [this]
    have he2 : |a^2*h^2*(s-x)/(x*s)| ≤ h^3 := by
      have hdx : 0 ≤ s-x := sub_nonneg.mpr hxs
      have hdh : s-x ≤ h := by
        have := hroot.1
        rw [abs_of_nonpos (sub_nonpos.mpr hxs)] at this
        linarith
      have ha2 : a^2 ≤ 1 := by
        have hh := pow_le_pow_left₀ (abs_nonneg a) ha 2
        simpa only [sq_abs, one_pow] using hh
      have hprod : a^2*h^2*(s-x) ≤ h^3 := by
        have h1 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg h)
        have h2 := mul_le_mul h1 hdh hdx (by positivity : 0 ≤ 1*h^2)
        nlinarith only [h2]
      rw [abs_of_nonneg (by positivity)]
      exact (div_le_self (by positivity) (by nlinarith : 1 ≤ x*s)).trans hprod
    rw [hid]
    exact (abs_add_le _ _).trans ((add_le_add he1 he2).trans_eq (by ring))
  have hf1 : |F1 - (-s*(2+b) + b*a*h)| ≤ 6 * h^2 := by
    let t := (s-x)/s
    let R := -Real.log (1-t)-t
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hxs) hs0.le
    have ht12 : t ≤ 1/2 := by
      apply (div_le_iff₀ hs0).mpr
      nlinarith
    have ht1 : 0 < 1-t := by linarith
    have hxt : x = s*(1-t) := by dsimp [t]; field_simp; ring
    have hulog : u = b/2 + Real.log (1-t) := by
      dsimp [u]
      rw [hxt, Real.log_mul hs0.ne' ht1.ne', hv]
    have hR0 : 0 ≤ R := by
      have ht := Real.log_le_sub_one_of_pos ht1
      dsimp [R]; linarith
    have hR : R ≤ t^2 := by
      have ht := D5.S3.Arith.Lattices.Klartag.neg_log_one_sub_le ht0 ht12
      dsimp [R]; linarith
    have hRabs : |R - b/2*t^2| ≤ t^2 := by
      have hv0 : 0 ≤ b/2*t^2 := mul_nonneg (by linarith only [hb0]) (sq_nonneg t)
      have hv1 : b/2*t^2 ≤ t^2 := by
        have := mul_le_mul_of_nonneg_right (show b/2 ≤ 1 by linarith only [hb1]) (sq_nonneg t)
        simpa only [one_mul] using this
      exact abs_le.mpr ⟨by linarith only [hR0, hv1], by linarith only [hR, hv0]⟩
    have hid : F1 - (-s*(2+b)) - b*δ = 4*(R-b/2*t^2)/x := by
      dsimp [F1, R, δ]
      rw [hulog]
      field_simp [hx0.ne']
      rw [hxt]
      ring_nf
      rw [hs2]
      <;> ring
    have herr : |F1 - (-s*(2+b)) - b*δ| ≤ 2*δ^2 := by
      rw [hid]
      apply (hdiv _).trans
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      have htδ : 4*t^2 = 2*δ^2 := by
        dsimp [t, δ]
        field_simp [hs0.ne']
        rw [hs2]
        ring
      linarith only [hRabs, htδ]
    have hd2 : δ^2 ≤ h^2 := by
      have hh := pow_le_pow_left₀ (abs_nonneg δ) hd 2
      simpa only [sq_abs] using hh
    have he2 : |b*(δ-a*h)| ≤ 4*h^2 := by
      rw [abs_mul, abs_of_nonneg hb0]
      calc
        b * |δ-a*h| ≤ b*(4*h^2) := mul_le_mul_of_nonneg_left hda hb0
        _ ≤ 4*h^2 := mul_le_of_le_one_left (by positivity) hb1
    have hid2 : F1 - (-s*(2+b)+b*a*h) =
        (F1 - (-s*(2+b)) - b*δ) + b*(δ-a*h) := by ring
    rw [hid2]
    have herr' : |F1 - (-s*(2+b)) - b*δ| ≤ 2*h^2 :=
      herr.trans (by nlinarith only [hd2])
    exact (abs_add_le _ _).trans ((add_le_add herr' he2).trans_eq (by ring))
  have hf2 : |F2 - s*(b^2+4*b+8)| ≤ 2*h := by
    have heval : 8*((Real.log s)^2+2*Real.log s+2)/s = s*(b^2+4*b+8) := by
      rw [hv]
      field_simp [hs0.ne']
      rw [hs2]
      ring
    have hh := profile_last_lipschitz hx hxs
    change |F2 - 8*((Real.log s)^2+2*Real.log s+2)/s| ≤ 2*|δ| at hh
    rw [heval] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
  have hrational : |x + (1/x)*(2/(1+z)-4*h/(1+z)^2+16*h^2/(1+z)^3) -
      (F0+h*F1+h^2*F2)| ≤ 62*h^3 := by
    have he1 : |1/(1+z)-(1-z+z^2)| ≤ z^3 := by
      have hid : 1/(1+z)-(1-z+z^2) = -z^3/(1+z) := by field_simp [hzv.ne']; ring
      rw [hid, abs_div, abs_neg, abs_pow, abs_of_nonneg hz0, abs_of_pos hzv]
      exact div_le_self (by positivity) (by linarith)
    have he2 : |1/(1+z)^2-(1-2*z)| ≤ 3*z^2 := by
      have hid : 1/(1+z)^2-(1-2*z) = z^2*(3+2*z)/(1+z)^2 := by field_simp [hzv.ne']; ring
      rw [hid, abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ (sq_pos_of_pos hzv)).mpr
      have hcoef : 3+2*z ≤ 3*(1+z)^2 := by nlinarith [sq_nonneg z]
      nlinarith only [mul_le_mul_of_nonneg_left hcoef (sq_nonneg z)]
    have he3 : |1/(1+z)^3-1| ≤ 3*z := by
      have hid : 1/(1+z)^3-1 = -z*(3+3*z+z^2)/(1+z)^3 := by field_simp [hzv.ne']; ring
      rw [hid, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz0) (by positivity)) (by positivity))]
      rw [← neg_div]
      apply (div_le_iff₀ (pow_pos hzv 3)).mpr
      have hcoef : 3+3*z+z^2 ≤ 3*(1+z)^3 := by
        nlinarith [sq_nonneg z, pow_nonneg hz0 3]
      nlinarith only [mul_le_mul_of_nonneg_left hcoef hz0]
    have he1h : |2*(1/(1+z)-(1-z+z^2))/x| ≤ 2*h^3 := by
      apply (hdiv _).trans
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
      have hz3 := pow_le_pow_left₀ hz0 hzh 3
      exact mul_le_mul_of_nonneg_left (he1.trans hz3) (by norm_num)
    have he2h : |(-4*h)*(1/(1+z)^2-(1-2*z))/x| ≤ 12*h^3 := by
      apply (hdiv _).trans
      rw [abs_mul, abs_of_nonpos (by nlinarith only [hh0] : -4*h ≤ 0)]
      have hz2 := pow_le_pow_left₀ hz0 hzh 2
      have he2' : |1/(1+z)^2-(1-2*z)| ≤ 3*h^2 :=
        he2.trans (by nlinarith only [hz2])
      have hmul := mul_le_mul_of_nonneg_left he2' (by positivity : 0 ≤ 4*h)
      nlinarith only [hmul]
    have he3h : |(16*h^2)*(1/(1+z)^3-1)/x| ≤ 48*h^3 := by
      apply (hdiv _).trans
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 16*h^2)]
      have he3' : |1/(1+z)^3-1| ≤ 3*h := he3.trans (by linarith only [hzh])
      have hmul := mul_le_mul_of_nonneg_left he3' (by positivity : 0 ≤ 16*h^2)
      nlinarith only [hmul]
    have hid : x + (1/x)*(2/(1+z)-4*h/(1+z)^2+16*h^2/(1+z)^3) -
        (F0+h*F1+h^2*F2) =
        (2*(1/(1+z)-(1-z+z^2))/x +
          (-4*h)*(1/(1+z)^2-(1-2*z))/x) + (16*h^2)*(1/(1+z)^3-1)/x := by
      dsimp [F0, F1, F2, z]
      ring
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add he1h he2h)) he3h) |>.trans_eq (by ring)
  have hpoly : |F0+h*F1+h^2*F2 -
      (2*s-s*(2+b)*h+s*(8+4*b+3*b^2/4)*h^2)| ≤ 17*h^3 := by
    have hcoeff : a^2/s+b*a+s*(b^2+4*b+8) = s*(8+4*b+3*b^2/4) := by
      dsimp [a]
      field_simp [hs0.ne']
      <;> ring
    have hid : F0+h*F1+h^2*F2 -
        (2*s-s*(2+b)*h+s*(8+4*b+3*b^2/4)*h^2) =
        ((F0-(2*s+(a^2/s)*h^2)) + h*(F1-(-s*(2+b)+b*a*h))) +
          h^2*(F2-s*(b^2+4*b+8)) := by rw [← hcoeff]; ring
    have hh1 : |h*(F1-(-s*(2+b)+b*a*h))| ≤ 6*h^3 := by
      rw [abs_mul, abs_of_nonneg hh0]
      have := mul_le_mul_of_nonneg_left hf1 hh0
      nlinarith only [this]
    have hh2 : |h^2*(F2-s*(b^2+4*b+8))| ≤ 2*h^3 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
      have := mul_le_mul_of_nonneg_left hf2 (sq_nonneg h)
      nlinarith only [this]
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add hf0 hh1)) hh2) |>.trans_eq (by ring)
  have hid : x + (1/x)*(2/(1+z)-4*h/(1+z)^2+16*h^2/(1+z)^3) -
      (2*s-s*(2+b)*h+s*(8+4*b+3*b^2/4)*h^2) =
      (x+(1/x)*(2/(1+z)-4*h/(1+z)^2+16*h^2/(1+z)^3)-(F0+h*F1+h^2*F2)) +
        (F0+h*F1+h^2*F2-(2*s-s*(2+b)*h+s*(8+4*b+3*b^2/4)*h^2)) := by ring
  change |x + (1/x)*(2/(1+z)-4*h/(1+z)^2+16*h^2/(1+z)^3) -
      (2*s-s*(2+b)*h+s*(8+4*b+3*b^2/4)*h^2)| ≤ 79*h^3
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add hrational hpoly).trans_eq (by ring))

private def a3 (t : ℝ) : ℝ :=
  1/(t*Real.log t)-1/(t*(Real.log t)^2)+2/(t*(Real.log t)^3)

private theorem root_profile_bound {X : ℝ} (hX : 2 ≤ X) (hL1 : 1 ≤ Real.log X) :
    |second_cutoff_root X / Real.sqrt X + Real.sqrt X * Real.log X * a3 (second_cutoff_root X) -
      (2 * Real.sqrt 2 - Real.sqrt 2 * (2 + Real.log 2) / Real.log X +
        Real.sqrt 2 * (8 + 4 * Real.log 2 + 3 * (Real.log 2)^2 / 4) / (Real.log X)^2)| ≤
      79 / (Real.log X)^3 := by
  let ρ := second_cutoff_root X
  let x := ρ / Real.sqrt X
  have hX0 : 0 < X := by linarith
  have hr : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  obtain ⟨hx, hxs, heq⟩ := root_normalized hX
  have hx0 : 0 < x := by dsimp [x, ρ]; positivity
  have hρ0 : 0 < ρ := by linarith [(second_cutoff_root_spec hX).1]
  have hρ : ρ = x * Real.sqrt X := by dsimp [x]; field_simp
  have hlog : Real.log ρ = Real.log x + Real.log X / 2 := by
    rw [hρ, Real.log_mul hx0.ne' hr.ne', Real.log_sqrt hX0.le]
  have hz : 1+2*(1/Real.log X)*Real.log x = 2*Real.log ρ/Real.log X := by
    rw [hlog]; field_simp; ring
  have hv : 0 < Real.log ρ := Real.log_pos (second_cutoff_root_spec hX).1
  have hh := profile_error (by positivity : 0 ≤ 1 / Real.log X)
    ((one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hL1).trans_eq (by norm_num)) hx hxs heq
  have hratio : Real.sqrt X / ρ = 1/x := by
    dsimp [x]
    field_simp [hρ0.ne', hr.ne']
  have hQ : x+Real.sqrt X*Real.log X*a3 ρ =
      x+(1/x)*(2/(1+2*(1/Real.log X)*Real.log x)-
        4*(1/Real.log X)/(1+2*(1/Real.log X)*Real.log x)^2+
        16*(1/Real.log X)^2/(1+2*(1/Real.log X)*Real.log x)^3) := by
    calc
      _ = x+(Real.sqrt X/ρ)*(Real.log X/Real.log ρ-
          Real.log X/(Real.log ρ)^2+2*Real.log X/(Real.log ρ)^3) := by dsimp [a3]; ring
      _ = _ := by
        rw [hratio, hz]
        field_simp [hx0.ne', hL.ne', hv.ne']
        <;> ring
  change |x + Real.sqrt X * Real.log X * a3 ρ - _| ≤ _
  rw [hQ]
  convert hh using 1 <;> congr 1 <;> ring

private theorem large_clock {X : ℝ} (hX : Real.exp 18 ≤ X) :
    18 ≤ Real.log X ∧ 46 < Real.sqrt X ∧ (Real.log X)^3 ≤ Real.sqrt X := by
  have hX0 : 0 < X := (Real.exp_pos 18).trans_le hX
  have hL : 18 ≤ Real.log X := by
    have := Real.log_le_log (Real.exp_pos 18) hX
    simpa only [Real.log_exp] using this
  have hL0 : 0 < Real.log X := by linarith
  have he18 := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 18) 5
  norm_num [Finset.sum_range_succ] at he18
  have hr : 46 < Real.sqrt X := by
    apply (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 46)).mpr
    linarith
  have he3 := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3) 6
  norm_num [Finset.sum_range_succ] at he3
  have hl18 : Real.log (18:ℝ) ≤ 3 := by
    have := Real.log_le_log (by norm_num : (0:ℝ)<18) (show 18 ≤ Real.exp 3 by linarith)
    simpa only [Real.log_exp] using this
  have hlL : Real.log (Real.log X) ≤ Real.log X / 6 := by
    have := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num : (0:ℝ)<18))
    rw [Real.log_div hL0.ne' (by norm_num : (18:ℝ)≠0)] at this
    linarith
  have hh := Real.exp_le_exp.mpr hlL
  rw [Real.exp_log hL0] at hh
  have hcube := pow_le_pow_left₀ hL0.le hh 3
  have heq : (Real.exp (Real.log X / 6))^3 = Real.sqrt X := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    have harg : (3:ℝ) * (Real.log X/6) = Real.log X/2 := by ring
    rw [harg, ← Real.log_sqrt hX0.le, Real.exp_log (Real.sqrt_pos.mpr hX0)]
  exact ⟨hL, hr, hcube.trans_eq heq⟩


set_option maxHeartbeats 600000 in
-- The finite endpoint, eighth-power theta and profile budgets are combined in one proof term.
/-- Both analytic thresholds are selected before the real clock and finite endpoint. -/
private theorem uniform_finite_lower :
    ∃ X0 : ℝ, 1 < X0 ∧ Real.exp 18 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ P : ℕ, (1 / (2 * Real.log 4)) * X ≤ (P : ℝ) →
      2 * Real.sqrt 2 - Real.sqrt 2 * (2 + Real.log 2) / Real.log X +
        Real.sqrt 2 * (8 + 4 * Real.log 2 + 3 * (Real.log 2)^2 / 4) / (Real.log X)^2 -
        3200 / (Real.log X)^3 ≤
      Real.sqrt X * Real.log X * (∑ p ∈ Nat.primesLE P,
        min (Real.log p / (X * Real.log X)) (-Real.log (1 - (p : ℝ)⁻¹ ^ 2))) := by
  obtain ⟨Y0, hY0, hA3⟩ := PriceRecord.PrimeSquareTail.prime_square_tail_logarithmic_refinements
  have herror : ∀ᶠ t : ℝ in atTop, |θ t - t| ≤ t / Real.log t ^ 8 := by
    filter_upwards [PriceRecord.LogarithmicLayerRigidity.theta_error_eight.eventuallyLE,
      eventually_gt_atTop (1 : ℝ)] with t ht ht1
    simpa only [Real.norm_eq_abs, abs_of_pos
      (div_pos (by linarith : 0 < t) (pow_pos (Real.log_pos ht1) 8))] using ht
  obtain ⟨T, hT⟩ := eventually_atTop.mp herror
  let T0 := max T (Real.exp 1 + 1)
  let X0 := max (Real.exp 18) (max (Y0^2) (T0^2))
  have he1 : 1 < Real.exp (1:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have hYpos : 0 < Y0 := by linarith
  have hTpos : 0 < T0 := by dsimp [T0]; exact lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hX018 : Real.exp 18 ≤ X0 := le_max_left _ _
  refine ⟨X0, lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hX018, hX018, ?_⟩
  intro X hX P hP
  have h18 := hX018.trans hX
  obtain ⟨hL18, hr46, hcube⟩ := large_clock h18
  let L := Real.log X
  let r := Real.sqrt X
  let ρ := second_cutoff_root X
  let x := ρ / r
  let h := 1/L
  let c : ℝ := 1 / (2*Real.log 4)
  let S := ∑ p ∈ (Ioc ⌊ρ⌋₊ P).filter Nat.Prime, (1:ℝ)/(p:ℝ)^2
  let H := θ ρ/(X*L)+S
  have hL : 0 < L := by dsimp [L]; linarith
  have hr : 0 < r := by dsimp [r]; linarith
  have hX0 : 0 < X := (Real.exp_pos 18).trans_le h18
  have hX2 : 2 ≤ X := by
    have := Real.add_one_le_exp (18:ℝ)
    linarith
  have hr2 : r^2 = X := Real.sq_sqrt hX0.le
  have hD : 0 < X*L := mul_pos hX0 hL
  have hrL : 0 < r*L := mul_pos hr hL
  obtain ⟨hρ1, hρr, hρhi, hρeq⟩ := second_cutoff_root_spec hX2
  change 1 < ρ at hρ1
  change r < ρ at hρr
  change ρ^2*Real.log ρ = X*L at hρeq
  have hρ0 : 0 < ρ := by linarith
  have hρs : ρ < Real.sqrt 2*r := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)] at hρhi
    exact hρhi
  have hx : 1 ≤ x := (le_div_iff₀ hr).mpr (by simpa using hρr.le)
  have hxs : x ≤ Real.sqrt 2 := (div_le_iff₀ hr).mpr hρs.le
  have hx0 : 0 < x := by linarith
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ1
  have hvL : L/2 ≤ Real.log ρ := by
    have := Real.log_le_log hr hρr.le
    rw [Real.log_sqrt hX0.le] at this
    exact this
  have hYρ : Y0 ≤ ρ := by
    have hYsq : Y0^2 ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
    have hYr : Y0 ≤ r := by nlinarith
    exact hYr.trans hρr.le
  have hTρ : T ≤ ρ := by
    have hTsq : T0^2 ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
    have hTr : T0 ≤ r := by nlinarith
    exact (le_max_left _ _).trans (hTr.trans hρr.le)
  have hb0 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hb1 : Real.log (2:ℝ) < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
    linarith
  have hl4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hc : 0 < c := by dsimp [c]; positivity
  have hc4 : 1/4 < c := by
    dsimp [c]
    apply (lt_div_iff₀ (by positivity : 0 < 2*Real.log (4:ℝ))).mpr
    rw [hl4]
    linarith
  have hcXρ : ρ < c*X := by
    have hs : Real.sqrt (2:ℝ) < 3/2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Real.sqrt_nonneg (2:ℝ)]
    have hrbig : 4*Real.sqrt 2 < r := by dsimp [r]; linarith
    have hcX : X/4 < c*X := by nlinarith [mul_pos (sub_pos.mpr hc4) hX0]
    have hsr : Real.sqrt 2*r < X/4 := by
      nlinarith [mul_pos hr (sub_pos.mpr hrbig)]
    exact hρs.trans (hsr.trans hcX)
  have hρP : ρ ≤ (P:ℝ) := (hcXρ.trans_le hP).le
  have hP0 : (0:ℝ) < P := hρ0.trans_le hρP
  have hlogP : L/2 ≤ Real.log (P:ℝ) :=
    hvL.trans (Real.log_le_log hρ0 hρP)
  have hlogP0 : 0 < Real.log (P:ℝ) := by linarith
  have hh0 : 0 ≤ h := by positivity
  have hh1 : h ≤ 1 := by
    apply (div_le_iff₀ hL).mpr
    dsimp [L]; linarith
  have hpow : h^8 ≤ h^3 := by
    have h5 : h^5 ≤ 1 := pow_le_one₀ hh0 hh1
    calc
      h^8 = h^3*h^5 := by ring
      _ ≤ h^3*1 := mul_le_mul_of_nonneg_left h5 (pow_nonneg hh0 3)
      _ = h^3 := by ring
  have hvInv : 1/Real.log ρ ≤ 2*h := by
    calc
      1/Real.log ρ ≤ 2/L := (div_le_div_iff₀ hlogρ hL).mpr (by linarith only [hvL])
      _ = 2*h := by dsimp [h]; ring
  have hheadError : x/(Real.log ρ)^8 ≤ 256*Real.sqrt 2*h^8 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1/Real.log ρ) hvInv 8
    have hi : (1/Real.log ρ)^8 = 1/(Real.log ρ)^8 := by ring
    rw [hi] at hp
    calc
      x/(Real.log ρ)^8 = x*(1/(Real.log ρ)^8) := by ring
      _ ≤ Real.sqrt 2*((2*h)^8) := mul_le_mul hxs hp (by positivity) (Real.sqrt_nonneg _)
      _ = 256*Real.sqrt 2*h^8 := by ring
  have hratio : r/ρ ≤ 1 := (div_le_one hρ0).mpr hρr.le
  have hfiniteError : r*L*(6/(ρ*(Real.log ρ)^4)+5/(ρ*(Real.log ρ)^9)) ≤
      96*h^3+2560*h^8 := by
    have h4 := pow_le_pow_left₀ (by positivity : 0 ≤ 1/Real.log ρ) hvInv 4
    have h9 := pow_le_pow_left₀ (by positivity : 0 ≤ 1/Real.log ρ) hvInv 9
    have he4 : r*L*(6/(ρ*(Real.log ρ)^4)) = 6*(r/ρ)*L*(1/Real.log ρ)^4 := by ring
    have he9 : r*L*(5/(ρ*(Real.log ρ)^9)) = 5*(r/ρ)*L*(1/Real.log ρ)^9 := by ring
    have hb4 : 6*(r/ρ)*L*(1/Real.log ρ)^4 ≤ 96*h^3 := by
      calc
        _ ≤ 6*1*L*(2*h)^4 := mul_le_mul
          (by nlinarith only [mul_le_mul_of_nonneg_right hratio hL.le]) h4
          (by positivity) (by positivity)
        _ = 96*h^3 := by dsimp [h]; field_simp; ring
    have hb9 : 5*(r/ρ)*L*(1/Real.log ρ)^9 ≤ 2560*h^8 := by
      calc
        _ ≤ 5*1*L*(2*h)^9 := mul_le_mul
          (by nlinarith only [mul_le_mul_of_nonneg_right hratio hL.le]) h9
          (by positivity) (by positivity)
        _ = 2560*h^8 := by dsimp [h]; field_simp; ring
    rw [mul_add, he4, he9]
    exact add_le_add hb4 hb9
  have hendpoint : r*L*a3 (P:ℝ) ≤ 16*h^3 := by
    let v := Real.log (P:ℝ)
    have hv : 0 < v := hlogP0
    have hv9 : 9 ≤ v := by dsimp [v]; dsimp [L] at hlogP; linarith
    have ha3 : a3 (P:ℝ) ≤ 2/((P:ℝ)*v) := by
      have hid : a3 (P:ℝ) = (v^2-v+2)/((P:ℝ)*v^3) := by
        dsimp [a3, v]; field_simp
      have hid2 : 2/((P:ℝ)*v) = (2*v^2)/((P:ℝ)*v^3) := by field_simp
      rw [hid, hid2]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith only [hv9, sq_nonneg v]
    have hnorm : r*L*(2/((P:ℝ)*v)) ≤ 4/(c*r) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (mul_pos hP0 hv) (mul_pos hc hr)).mpr
      have hpv := mul_le_mul hP hlogP (by linarith only [hL] : 0 ≤ L/2) hP0.le
      have hpv' : c*r^2*L ≤ 2*(P:ℝ)*v := by
        rw [hr2]
        dsimp only [v]
        nlinarith only [hpv]
      nlinarith only [hpv']
    have hscale : 4/(c*r) ≤ (4/c)*h^3 := by
      have hcub : L^3 ≤ r := hcube
      have hi := one_div_le_one_div_of_le (pow_pos hL 3) hcub
      have hh : (1:ℝ)/L^3 = h^3 := by dsimp [h]; ring
      rw [hh] at hi
      have := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 4/c)
      convert this using 1 <;> ring
    have hconst : 4/c ≤ 16 := by
      dsimp [c]
      rw [hl4]
      have hid : (4:ℝ)/(1/(2*(2*Real.log 2))) = 16*Real.log 2 := by field_simp; ring
      rw [hid]
      linarith
    exact (mul_le_mul_of_nonneg_left ha3 hrL.le).trans (hnorm.trans
      (hscale.trans (mul_le_mul_of_nonneg_right hconst (pow_nonneg hh0 3))))
  have hprof := root_profile_bound hX2 (by linarith only [hL18])
  change |x+r*L*a3 ρ -
    (2*Real.sqrt 2-Real.sqrt 2*(2+Real.log 2)/L+
      Real.sqrt 2*(8+4*Real.log 2+3*(Real.log 2)^2/4)/L^2)| ≤ 79/L^3 at hprof
  have hA := (hA3 ρ (P:ℝ) hYρ hρP).2
  simp only [Nat.floor_natCast] at hA
  change |S-a3 ρ+a3 (P:ℝ)| ≤ 6/(ρ*(Real.log ρ)^4)+5/(ρ*(Real.log ρ)^9) at hA
  have hθ := hT ρ hTρ
  have hslow : a3 ρ-a3 (P:ℝ)-(6/(ρ*(Real.log ρ)^4)+5/(ρ*(Real.log ρ)^9)) ≤ S := by
    linarith only [(abs_le.mp hA).1]
  have hθlow : ρ-ρ/(Real.log ρ)^8 ≤ θ ρ := by linarith only [(abs_le.mp hθ).1]
  have hH : x+r*L*a3 ρ-x/(Real.log ρ)^8-
      r*L*(6/(ρ*(Real.log ρ)^4)+5/(ρ*(Real.log ρ)^9))-r*L*a3 (P:ℝ) ≤ r*L*H := by
    have hle := mul_le_mul_of_nonneg_left (add_le_add
      (div_le_div_of_nonneg_right hθlow hD.le) hslow) hrL.le
    convert hle using 1
    · dsimp only [x]
      rw [← hr2]
      field_simp [hr.ne', hL.ne', hρ0.ne', hlogρ.ne']
      <;> ring
  have hs15 : Real.sqrt (2:ℝ) < 3/2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Real.sqrt_nonneg (2:ℝ)]
  have hbudget : 79*h^3 + 256*Real.sqrt 2*h^8 + (96*h^3+2560*h^8) +16*h^3 ≤ 3200*h^3 := by
    have hp1 := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 256*Real.sqrt 2)
    have hp2 := mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤2560)
    have hp3 := mul_le_mul_of_nonneg_right hs15.le (pow_nonneg hh0 3)
    nlinarith only [hp1, hp2, hp3, pow_nonneg hh0 3]
  have hfinite := finite_root_prime_min_lower (by linarith : 1<X) hρ1 hρeq hρP
  have hscaled := mul_le_mul_of_nonneg_left hfinite hrL.le
  have heq79 : 79/L^3 = 79*h^3 := by dsimp [h]; ring
  have heq3200 : 3200/L^3 = 3200*h^3 := by dsimp [h]; ring
  rw [heq79] at hprof
  rw [heq3200]
  change _ ≤ r*L*_
  change r*L*H ≤ _ at hscaled
  have hproflower := (abs_le.mp hprof).1
  linarith only [hH, hscaled, hproflower, hheadError, hfiniteError, hendpoint, hbudget]


/-- One threshold controls the actual complete tail of every initial-support integer. -/
theorem uniform_min_tail_robin_second_order_lower :
    ∃ X0 : ℝ, 1 < X0 ∧ ∀ m P : ℕ, 0 < m →
      m.primeFactors = Nat.primesLE P →
      1 < Chebyshev.theta (P : ℝ) →
      X0 ≤ Real.log (m : ℝ) →
      let X := Real.log (m : ℝ)
      let L := Real.log X
      2 * Real.sqrt 2 - Real.sqrt 2 * (2 + Real.log 2) / L +
        Real.sqrt 2 * (8 + 4 * Real.log 2 + 3 * (Real.log 2)^2 / 4) / L^2 -
        3200 / L^3 ≤
      Real.sqrt X * L * (OriginalEndpointPrimeTail.tail m +
        Real.log (Real.log X) - Real.log (Real.log (Chebyshev.theta (P : ℝ)))) := by
  obtain ⟨X0, hX01, hX018, hbound⟩ := uniform_finite_lower
  refine ⟨X0, hX01, ?_⟩
  intro m P hm hsupport htheta hXm
  let X := Real.log (m:ℝ)
  let L := Real.log X
  let Q := largestPrime m
  have hQP : Q ≤ P := by
    dsimp [Q, largestPrime]
    apply Finset.sup_le
    intro p hp
    have hpP : p ∈ Nat.primesLE P := hsupport ▸ hp
    exact (Nat.mem_primesLE.mp hpP).1
  have hsQ : m.primeFactors = Nat.primesLE Q := by
    ext p
    constructor
    · intro hp
      have hpP : p ∈ Nat.primesLE P := hsupport ▸ hp
      refine Nat.mem_primesLE.mpr ⟨?_, (Nat.mem_primesLE.mp hpP).2⟩
      simpa only [Q, largestPrime, id_eq] using
        (Finset.le_sup (f := id) hp)
    · intro hp
      rw [hsupport]
      exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hQP,
        (Nat.mem_primesLE.mp hp).2⟩
  have hθQ : θ (P:ℝ) = θ (Q:ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
      ← hsupport, ← hsQ]
  have hthetaQ : 1 < θ (Q:ℝ) := by simpa only [hθQ] using htheta
  have h18 : Real.exp 18 ≤ X := hX018.trans hXm
  obtain ⟨hL18, hr46, _⟩ := large_clock h18
  have hX1 : 1 < X := hX01.trans_le hXm
  have hX0 : 0 < X := by linarith
  have hL : 0 < L := Real.log_pos hX1
  have hr : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hrL : 0 < Real.sqrt X*L := mul_pos hr hL
  by_cases hhalf : X/2 ≤ θ (P:ℝ)
  · have hcheb := Chebyshev.theta_le_log4_mul_x (x := (P:ℝ)) (Nat.cast_nonneg _)
    have hratio : (1/(2*Real.log 4))*X ≤ (P:ℝ) := by
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<2*Real.log 4)).mpr
      nlinarith only [hhalf, hcheb]
    have hmin := hbound X hXm P hratio
    rw [← hsupport] at hmin
    have hfinite := (finite_min_tail_robin_bound hm hsQ hthetaQ).1
    rw [← hθQ] at hfinite
    have hscaled := mul_le_mul_of_nonneg_left hfinite hrL.le
    exact hmin.trans hscaled
  · have hgap : θ (P:ℝ) < X/2 := lt_of_not_ge hhalf
    have ht := RestrictedDivisorStrictInventory.loglog_tangent
      (x := X) (y := θ (P:ℝ)) hX1 htheta (by linarith)
    have ht' : Real.log (Real.log (θ (P:ℝ))) - Real.log (Real.log X) <
        (θ (P:ℝ)-X)/(X*L) := by
      simpa only [ActualRobinClockCovariance.g, div_eq_mul_inv, one_mul, L] using ht
    have hclock : 1/(2*L) < Real.log (Real.log X)-Real.log (Real.log (θ (P:ℝ))) := by
      have hcharge : 1/(2*L) < (X-θ (P:ℝ))/(X*L) := by
        apply (div_lt_div_iff₀ (by positivity : 0<2*L) (mul_pos hX0 hL)).mpr
        nlinarith only [mul_pos (by linarith : 0<X/2-θ (P:ℝ)) hL]
      have hflip : (X-θ (P:ℝ))/(X*L) <
          Real.log (Real.log X)-Real.log (Real.log (θ (P:ℝ))) := by
        rw [sub_div] at ht' ⊢
        linarith only [ht']
      exact hcharge.trans hflip
    have htail := (tail_robin_data hm hsQ).1
    have hA : 1/(2*L) < tail m+Real.log (Real.log X)-Real.log (Real.log (θ (P:ℝ))) := by
      linarith only [hclock, htail]
    have hnorm : Real.sqrt X/2 < Real.sqrt X*L*
        (tail m+Real.log (Real.log X)-Real.log (Real.log (θ (P:ℝ)))) := by
      have hh := mul_lt_mul_of_pos_left hA hrL
      convert hh using 1
      field_simp
    have hb0 : 0 ≤ Real.log (2:ℝ) := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    have hb1 : Real.log (2:ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith
    have hb2 : (Real.log (2:ℝ))^2 ≤ 1 := by nlinarith
    have hs0 : 0 ≤ Real.sqrt (2:ℝ) := Real.sqrt_nonneg _
    have hs15 : Real.sqrt (2:ℝ) < 3/2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    have hc20 : 0 ≤ Real.sqrt 2*(8+4*Real.log 2+3*(Real.log 2)^2/4) := by positivity
    have hc2 : Real.sqrt 2*(8+4*Real.log 2+3*(Real.log 2)^2/4) ≤
        (51/4)*Real.sqrt 2 := by
      have := mul_le_mul_of_nonneg_left
        (show 8+4*Real.log 2+3*(Real.log 2)^2/4 ≤ (51/4:ℝ) by nlinarith) hs0
      nlinarith only [this]
    have hfrac : Real.sqrt 2*(8+4*Real.log 2+3*(Real.log 2)^2/4)/L^2 ≤
        Real.sqrt 2*(8+4*Real.log 2+3*(Real.log 2)^2/4) :=
      div_le_self hc20 (by dsimp [L] at *; nlinarith)
    have hsmall : 2*Real.sqrt 2-Real.sqrt 2*(2+Real.log 2)/L+
        Real.sqrt 2*(8+4*Real.log 2+3*(Real.log 2)^2/4)/L^2-3200/L^3 < 23 := by
      have hneg1 : 0 ≤ Real.sqrt 2*(2+Real.log 2)/L := by positivity
      have hneg3 : 0 ≤ (3200:ℝ)/L^3 := by positivity
      linarith
    exact (hsmall.trans (by dsimp [X] at *; linarith : 23 < Real.sqrt X/2)).le.trans hnorm.le

#print axioms uniform_min_tail_robin_second_order_lower

end
end D5.S3.Arith.Robin.PrimeMinCorrectionSecondOrderLower
