/- GID: D5/S3/Arith/Robin/PrimeMinCorrectionSecondOrderLower
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimeMinCorrectionSecondOrderLower
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: A uniform three-term lower correction for every initial prime support. -/

import D5.S3.Arith.Robin.PrimeMinCorrectionLower
import D5.S3.Arith.Robin.EulerLayer.EulerLayerRootSecondOrder
import D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
import Mathlib.Analysis.Calculus.MeanValue

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
      change (x+s)*(s/2-q) ≤ (x+s)*(s-x)
      nlinarith only [hqq, hs2]
  have hugap : 0 ≤ b / 2 - u ∧ b / 2 - u ≤ d := by
    have ht := Real.log_le_sub_one_of_pos (div_pos hs0 hx0)
    rw [Real.log_div hs0.ne' hx0.ne', hv] at ht
    have hgap : b / 2 - u ≤ (s - x) / x := by
      convert ht using 1 <;> dsimp [u] <;> field_simp <;> ring
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
      _ = h*(2*(q*(x+s))*u) := by rw [hqq]
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
    dsimp only [S, H]
    simp only [mem_sdiff, Nat.mem_primesLE, mem_filter, mem_Ioc]
    omega
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
      simpa only [one_mul] using hmono.le
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
    convert hh' using 1 <;> dsimp [F, F']
    field_simp
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
    apply (neg_div_le_iff₀ (sq_pos_of_pos ht0)).mpr
    nlinarith [sq_nonneg (Real.log t), sq_nonneg t]
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbnd
    (convex_Icc (1 : ℝ) (Real.sqrt 2)) (show Real.sqrt 2 ∈ Set.Icc 1 (Real.sqrt 2) from
      ⟨hs, le_rfl⟩) (show x ∈ Set.Icc 1 (Real.sqrt 2) from ⟨hx, hxs⟩)
  simpa only [Real.norm_eq_abs, F] using hh

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
  have hu : u ≤ b / 2 := by simpa only [hv] using Real.log_le_log hx0 hxs
  have hz0 : 0 ≤ z := by positivity
  have hzh : z ≤ h := by dsimp [z]; nlinarith
  have hzv : 0 < 1 + z := by positivity
  have hdiv (w : ℝ) : |w / x| ≤ |w| := by
    rw [abs_div, abs_of_pos hx0]
    exact div_le_self (abs_nonneg _) hx
  have hroot := root_error hh0 hx hxs heq
  have hd : |δ| ≤ h := hroot.1
  have hda : |δ - a * h| ≤ 4 * h^2 := by simpa [δ, a] using hroot.2
  have ha : |a| ≤ 1 := by
    rw [abs_of_nonpos (by dsimp [a]; positivity)]
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
      field_simp
      nlinarith only [hs2]
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
      have ha2 : a^2 ≤ 1 := by nlinarith [sq_abs a]
      have hprod : a^2*h^2*(s-x) ≤ h^3 := by
        have h1 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg h)
        have h2 := mul_le_mul h1 hdh hdx (sq_nonneg h)
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
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg t]
    have hid : F1 - (-s*(2+b)) - b*δ = 4*(R-b/2*t^2)/x := by
      dsimp [F1, R, δ]
      rw [hulog]
      field_simp
      nlinarith only [hs2, hxt]
    have herr : |F1 - (-s*(2+b)) - b*δ| ≤ 2*δ^2 := by
      rw [hid]
      apply (hdiv _).trans
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      have htδ : 4*t^2 = 2*δ^2 := by
        dsimp [t, δ]
        field_simp
        nlinarith only [hs2]
      linarith
    have hd2 : δ^2 ≤ h^2 := by nlinarith [sq_abs δ, sq_nonneg (h-|δ|)]
    have he2 : |b*(δ-a*h)| ≤ 4*h^2 := by
      rw [abs_mul, abs_of_nonneg hb0]
      calc
        b * |δ-a*h| ≤ b*(4*h^2) := mul_le_mul_of_nonneg_left hda hb0
        _ ≤ 4*h^2 := mul_le_of_le_one_left (by positivity) hb1
    have hid2 : F1 - (-s*(2+b)+b*a*h) =
        (F1 - (-s*(2+b)) - b*δ) + b*(δ-a*h) := by ring
    rw [hid2]
    exact (abs_add_le _ _).trans ((add_le_add (herr.trans (by nlinarith)) he2).trans_eq (by ring))
  have hf2 : |F2 - s*(b^2+4*b+8)| ≤ 2*h := by
    have heval : 8*((Real.log s)^2+2*Real.log s+2)/s = s*(b^2+4*b+8) := by
      rw [hv]
      field_simp
      nlinarith only [hs2]
    have hh := profile_last_lipschitz hx hxs
    change |F2 - 8*((Real.log s)^2+2*Real.log s+2)/s| ≤ 2*|δ| at hh
    rw [heval] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
  have hrational : |x + (1/x)*(2/(1+z)-4*h/(1+z)^2+16*h^2/(1+z)^3) -
      (F0+h*F1+h^2*F2)| ≤ 62*h^3 := by
    have he1 : |1/(1+z)-(1-z+z^2)| ≤ z^3 := by
      have hid : 1/(1+z)-(1-z+z^2) = -z^3/(1+z) := by field_simp; ring
      rw [hid, abs_div, abs_neg, abs_pow, abs_of_nonneg hz0, abs_of_pos hzv]
      exact div_le_self (by positivity) (by linarith)
    have he2 : |1/(1+z)^2-(1-2*z)| ≤ 3*z^2 := by
      have hid : 1/(1+z)^2-(1-2*z) = z^2*(3+2*z)/(1+z)^2 := by field_simp; ring
      rw [hid, abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ (sq_pos_of_pos hzv)).mpr
      have hcoef : 3+2*z ≤ 3*(1+z)^2 := by nlinarith [sq_nonneg z]
      nlinarith only [mul_le_mul_of_nonneg_left hcoef (sq_nonneg z)]
    have he3 : |1/(1+z)^3-1| ≤ 3*z := by
      have hid : 1/(1+z)^3-1 = -z*(3+3*z+z^2)/(1+z)^3 := by field_simp; ring
      rw [hid, abs_of_nonpos (by positivity)]
      apply (neg_div_le_iff₀ (pow_pos hzv 3)).mpr
      have hcoef : 3+3*z+z^2 ≤ 3*(1+z)^3 := by
        nlinarith [sq_nonneg z, pow_nonneg hz0 3]
      nlinarith only [mul_le_mul_of_nonneg_left hcoef hz0]
    have he1h : |2*(1/(1+z)-(1-z+z^2))/x| ≤ 2*h^3 := by
      apply (hdiv _).trans
      rw [abs_mul]
      norm_num
      have hz3 := pow_le_pow_left₀ hz0 hzh 3
      linarith
    have he2h : |(-4*h)*(1/(1+z)^2-(1-2*z))/x| ≤ 12*h^3 := by
      apply (hdiv _).trans
      rw [abs_mul, abs_of_nonpos (by positivity : -4*h ≤ 0)]
      have hz2 := pow_le_pow_left₀ hz0 hzh 2
      have hmul := mul_le_mul_of_nonneg_left (he2.trans (by nlinarith)) (by positivity : 0 ≤ 4*h)
      nlinarith only [hmul]
    have he3h : |(16*h^2)*(1/(1+z)^3-1)/x| ≤ 48*h^3 := by
      apply (hdiv _).trans
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 16*h^2)]
      have hmul := mul_le_mul_of_nonneg_left (he3.trans (by linarith)) (by positivity : 0 ≤ 16*h^2)
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
      field_simp
      nlinarith only [hs2]
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
  change |x + Real.sqrt X * Real.log X * a3 ρ - _| ≤ _
  convert hh using 1
  · congr 1
    rw [hz]
    dsimp [a3]
    rw [hρ]
    field_simp
    <;> ring
  · field_simp

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
    have harg : (3:ℝ) * (Real.log X/6) = Real.log X/2 := by ring
    rw [harg, ← Real.log_sqrt hX0.le, Real.exp_log (Real.sqrt_pos.mpr hX0)]
  exact ⟨hL, hr, hcube.trans_eq heq⟩

end
end D5.S3.Arith.Robin.PrimeMinCorrectionSecondOrderLower
