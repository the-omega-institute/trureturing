/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/SeparatedFourRadicalSign
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict negativity of the separated radical mixed derivative at gap four. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedFourRadicalAverage
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripMarginal
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterShortGapCorrection

/-! # The separated radical sign at gap four -/

open Filter Set
open scoped Topology

namespace RefinedBMV.PositiveCenter

open private radicalRateFactor radicalRateFactorDeriv hasDerivAt_decay
  hasDerivAt_radicalRateFactor upperTailRadicalRoot_pos hasDerivAt_upperTailRadicalRoot
  hasDerivAt_radicalRootDeriv sub_le_sub_of_derivatives scaled_exponential_ratio_lower
  radicalLeftFactor radicalUpperFactor radicalGapFactor radicalFactorization
  radicalLeftFactor_jet radicalUpperFactor_jet radicalGapFactor_jet
  separatedGapRadicalContribution_eq from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterSeparatedGapRadical

open private shortGap_exp_neg_four_le shortGap_root_lower from
  D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterShortGapCorrection

private theorem radical_rate_slope_bounds {h t : ℝ} (hh : 0 < h) (ht : 4 ≤ t) :
    0 < radicalRateFactor h t ∧
      0 ≤ radicalRateFactorDeriv h t / radicalRateFactor h t ∧
      radicalRateFactorDeriv h t / radicalRateFactor h t ≤ 1 / (t - 1) := by
  let H := radicalRateFactor h
  let K := radicalRateFactorDeriv h
  let A := (1 + h) * Real.exp (-(h * t))
  have ht₀ : 0 ≤ t := by linarith
  have ht₁ : 0 < t - 1 := by linarith
  have hj : 0 < 1 + h := by linarith
  have hA : 0 < A := mul_pos hj (Real.exp_pos _)
  have hK (s : ℝ) : K s = ((1 + h) * Real.exp (-(h * s))) * (1 - Real.exp (-s)) := by
    change (1 + h) * (Real.exp (-(h * s)) - Real.exp (-((1 + h) * s))) = _
    rw [show -((1 + h) * s) = -(h * s) + -s by ring, Real.exp_add]
    ring
  have he (s : ℝ) (hs : 0 ≤ s) : 0 ≤ 1 - Real.exp (-s) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs))
  have hprimitive (s : ℝ) :
      HasDerivAt (fun x ↦ A * (x - 1 + Real.exp (-x))) (A * (1 - Real.exp (-s))) s := by
    have hdecay : HasDerivAt (fun x : ℝ ↦ Real.exp (-x)) (-Real.exp (-s)) s := by
      simpa only [one_mul, neg_one_mul] using hasDerivAt_decay 1 s
    simpa only [Pi.add_apply, sub_eq_add_neg] using
      (((hasDerivAt_id' s).sub_const 1).add hdecay).const_mul A
  have hbase := sub_le_sub_of_derivatives ht₀ (fun s _ ↦ hprimitive s)
    (fun _ _ ↦ hasDerivAt_radicalRateFactor hh) (fun s hs ↦ by
      change A * (1 - Real.exp (-s)) ≤ K s
      rw [hK]
      apply mul_le_mul_of_nonneg_right _ (he s hs.1)
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hs.2 hh.le))) hj.le)
  have hH₀ : H 0 = 0 := by simp [H, radicalRateFactor, upperTailGap]
  change A * (t - 1 + Real.exp (-t)) - A * (0 - 1 + Real.exp (-(0 : ℝ))) ≤ H t - H 0 at hbase
  simp only [hH₀, neg_zero, Real.exp_zero, zero_sub, neg_add_cancel, mul_zero, sub_zero] at hbase
  have hHt : A * (t - 1) ≤ H t :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_pos _).le) hA.le).trans hbase
  have hH : 0 < H t := (mul_pos hA ht₁).trans_le hHt
  have hKt : K t ≤ A := by
    rw [hK]
    exact mul_le_of_le_one_right hA.le (sub_le_self 1 (Real.exp_pos _).le)
  change 0 < H t ∧ 0 ≤ K t / H t ∧ K t / H t ≤ 1 / (t - 1)
  refine ⟨hH, div_nonneg (by rw [hK]; exact mul_nonneg hA.le (he t ht₀)) hH.le, ?_⟩
  apply (div_le_div_iff₀ hH ht₁).mpr
  simpa only [one_mul] using (mul_le_mul_of_nonneg_right hKt ht₁.le).trans hHt

private theorem radical_root_relative_slope_le {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 4 ≤ t) : deriv (upperTailRadicalRoot h) t / upperTailRadicalRoot h t ≤ 1 / 20 := by
  let z := upperTailRadicalRoot h
  let a := upperTailGap h t
  let c := (3 + h) * (3 + 2 * h) / 2
  have ht₀ : 0 < t := by linarith
  have ha : 0 < a := tail_gap_pos hh ht₀
  have hc : c ≤ 6 := by
    dsimp only [c]
    nlinarith only [hhmax, mul_le_mul_of_nonneg_left hhmax hh.le]
  have hdecay : a * Real.exp (-t) ≤ 4 / 52 := calc
    _ ≤ t * Real.exp (-t) := mul_le_mul_of_nonneg_right (upperTailGap_le hh) (Real.exp_pos _).le
    _ ≤ (4 * Real.exp (t - 4)) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right (by linarith only [Real.add_one_le_exp (t - 4), ht])
        (Real.exp_pos _).le
    _ = 4 * Real.exp (-4) := by rw [mul_assoc, ← Real.exp_add, show t - 4 + -t = -4 by ring]
    _ ≤ _ := by linarith only [shortGap_exp_neg_four_le]
  have hquad : c * a ^ 2 * Real.exp (-(2 * t)) ≤ 96 / 52 ^ 2 := calc
    _ = c * (a * Real.exp (-t)) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      simp only [Nat.cast_ofNat, mul_neg, mul_assoc]
    _ ≤ 6 * (4 / 52 : ℝ) ^ 2 := mul_le_mul hc
      (pow_le_pow_left₀ (mul_nonneg ha.le (Real.exp_pos _).le) hdecay 2)
      (sq_nonneg _) (by norm_num)
    _ = _ := by norm_num
  have hT := (shortGap_marginal_deriv_bounds hh hhmax ht).2
  change deriv z t ≤ (51 / 50) * (c * a ^ 2 * Real.exp (-(2 * t))) at hT
  have hz : (50 / 51 : ℝ) ≤ z t := shortGap_root_lower hh hhmax ht
  apply (div_le_iff₀ (upperTailRadicalRoot_pos hh ht₀)).mpr
  calc
    deriv z t ≤ (51 / 50) * (96 / 52 ^ 2) :=
      hT.trans (mul_le_mul_of_nonneg_left hquad (by norm_num))
    _ ≤ (1 / 20) * (50 / 51) := by norm_num
    _ ≤ (1 / 20) * z t := mul_le_mul_of_nonneg_left hz (by norm_num)

/-- The positive radical density has a uniform logarithmic slope window at gaps at least four. -/
theorem separatedFour_radical_logDeriv_bounds {h t : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (ht : 4 ≤ t) :
    let T := deriv (upperTailRadicalRoot h)
    0 < T t ∧ DifferentiableAt ℝ T t ∧
      -(41 / 20 : ℝ) ≤ deriv T t / T t ∧ deriv T t / T t ≤ -(17 / 12 : ℝ) := by
  let z := upperTailRadicalRoot h
  let T := deriv z
  have ht₀ : 0 < t := by linarith
  obtain ⟨hH, hK₀, hK⟩ := radical_rate_slope_bounds hh ht
  have hT : 0 < T t := by
    change 0 < deriv (upperTailRadicalRoot h) t
    rw [(hasDerivAt_upperTailRadicalRoot hh ht₀).deriv]
    have ha := tail_gap_pos hh ht₀
    have hz := upperTailRadicalRoot_pos hh ht₀
    exact div_pos (mul_pos (mul_pos (mul_pos (by positivity) (Real.exp_pos _)) ha) hH) hz
  have hTd := hasDerivAt_radicalRootDeriv hh ht₀ hH
  have hLs := upperTailSlope_bounds hh ht₀
  have hL := hLs.2.1.trans (one_div_le_one_div_of_le (by norm_num) ht)
  have hKmax := hK.trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3)
    (by linarith only [ht] : (3 : ℝ) ≤ t - 1))
  have hrel := radical_root_relative_slope_le hh hhmax ht
  have hrel₀ : 0 ≤ T t / z t := div_nonneg hT.le (upperTailRadicalRoot_pos hh ht₀).le
  refine ⟨hT, hTd.differentiableAt, ?_⟩
  change -(41 / 20 : ℝ) ≤ deriv T t / T t ∧ deriv T t / T t ≤ -(17 / 12 : ℝ)
  rw [hTd.deriv, mul_div_cancel_left₀ _ hT.ne']
  constructor <;> linarith only [hLs.1, hL, hK₀, hKmax, hrel, hrel₀]

/-- The transferred slope and ratio bounds for a radical divided difference at gap four. -/
private theorem radical_dividedDifference_bounds {h d v : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (hd : 4 ≤ d) (hdv : d < v) :
    let z := upperTailRadicalRoot h
    let T := deriv z
    let D := z v - z d
    0 < D ∧ (T v - T d) / D ≤ -(17 / 12 : ℝ) ∧
      deriv T d / T d - (T v - T d) / D ≤ 3 * (v - d) / (d * (d + v)) ∧
      (17 / 12) / (1 - Real.exp (-((17 / 12) * (v - d)))) ≤ T d / D ∧
      T d / D ≤ 1 / (v - d) + 41 / 20 := by
  let z := upperTailRadicalRoot h
  let T := deriv z
  let D := z v - z d
  let rho (s : ℝ) := deriv T s / T s
  let r : ℝ := 17 / 12
  let ν : ℝ := 41 / 20
  have hr : 0 < r := by norm_num [r]
  have hvd : 0 < v - d := sub_pos.mpr hdv
  have hz (s : ℝ) (hs : 4 ≤ s) : HasDerivAt z (T s) s :=
    (hasDerivAt_upperTailRadicalRoot hh (by linarith)).differentiableAt.hasDerivAt
  have hbounds (s : ℝ) (hs : 4 ≤ s) :
      0 < T s ∧ DifferentiableAt ℝ T s ∧ -ν ≤ rho s ∧ rho s ≤ -r :=
    separatedFour_radical_logDeriv_bounds hh hhmax hs
  have hT (s : ℝ) (hs : 4 ≤ s) : HasDerivAt T (rho s * T s) s :=
    ((hbounds s hs).2.1.hasDerivAt).congr_deriv
      (by dsimp only [rho]; rw [div_mul_cancel₀ _ (hbounds s hs).1.ne'])
  have hzmono : StrictMonoOn z (Ici 4) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun s hs ↦ (hz s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [(hz s (interior_subset hs)).deriv]
      exact (hbounds s (interior_subset hs)).1
  have hD : 0 < D := sub_pos.mpr (hzmono hd (hd.trans hdv.le) hdv)
  have hsec (a b : ℝ) (ha : 4 ≤ a) (hab : a ≤ b) :
      T b - T a ≤ -r * (z b - z a) := by
    have hi := sub_le_sub_of_derivatives hab (fun s hs ↦ hT s (ha.trans hs.1))
      (fun s hs ↦ (hz s (ha.trans hs.1)).const_mul (-r))
      (fun s hs ↦ mul_le_mul_of_nonneg_right (hbounds s (ha.trans hs.1)).2.2.2
        (hbounds s (ha.trans hs.1)).1.le)
    exact hi.trans_eq (by ring)
  have hM : (T v - T d) / D ≤ -r := (div_le_iff₀ hD).mpr (hsec d v hd hdv.le)
  have hmean := separatedFour_radical_root_dividedDifference_average hh hd hdv
    (fun s hs ↦ (hbounds s (hd.trans hs.1)).2.2.2)
  have hsecLower : -ν * D ≤ T v - T d := by
    have hi := sub_le_sub_of_derivatives hdv.le
      (fun s hs ↦ (hz s (hd.trans hs.1)).const_mul (-ν)) (fun s hs ↦ hT s (hd.trans hs.1))
      (fun s hs ↦ mul_le_mul_of_nonneg_right (hbounds s (hd.trans hs.1)).2.2.1
        (hbounds s (hd.trans hs.1)).1.le)
    exact le_trans (le_of_eq (by dsimp only [D]; ring)) hi
  have hfloor : T v * (v - d) ≤ D := by
    have hi := sub_le_sub_of_derivatives hdv.le
      (fun s _ ↦ hasDerivAt_const_mul (x := s) (T v)) (fun s hs ↦ hz s (hd.trans hs.1))
      (fun s hs ↦ by
        have hs' : 4 ≤ s := hd.trans hs.1
        have h := hsec s v hs' hs.2
        have hzle := hzmono.monotoneOn hs' (hd.trans hdv.le) hs.2
        exact sub_nonpos.mp (h.trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le)
          (sub_nonneg.mpr hzle))))
    exact le_trans (le_of_eq (by ring)) hi
  have hRupper : T d / D ≤ 1 / (v - d) + ν := by
    apply (div_le_iff₀ hD).mpr
    have hfloor' := (le_div_iff₀ hvd).mpr hfloor
    calc
      T d ≤ T v + ν * D := by linarith only [hsecLower]
      _ ≤ D / (v - d) + ν * D := add_le_add_left hfloor' _
      _ = _ := by ring
  let W (s : ℝ) := Real.exp (r * (s - d)) * (r * (z s - z d) - T d)
  have hW (s : ℝ) (hs : s ∈ Icc d v) :
      HasDerivAt W (Real.exp (r * (s - d)) * r * (T s - T d + r * (z s - z d))) s := by
    have he : HasDerivAt (fun x ↦ Real.exp (r * (x - d))) (Real.exp (r * (s - d)) * r) s := by
      simpa only [mul_one] using (((hasDerivAt_id' s).sub_const d).const_mul r).exp
    have hdiff := (((hz s (hd.trans hs.1)).sub_const (z d)).const_mul r).sub_const (T d)
    apply (he.mul hdiff).congr_deriv
    ring
  have hWle := sub_le_sub_of_derivatives hdv.le hW (fun s _ ↦ hasDerivAt_const s (0 : ℝ))
    (fun s hs ↦ mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Real.exp_pos _).le hr.le)
      (by linarith only [hsec d s hd hs.1]))
  have hWd : W d = -T d := by simp [W]
  simp only [hWd, sub_self] at hWle
  have hw := mul_le_mul_of_nonneg_left (sub_nonpos.mp hWle) (Real.exp_pos (-(r * (v - d)))).le
  change Real.exp (-(r * (v - d))) * (Real.exp (r * (v - d)) * (r * D - T d)) ≤ _ at hw
  rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hw
  have he : 0 < 1 - Real.exp (-(r * (v - d))) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hr hvd)))
  have hRlower : r / (1 - Real.exp (-(r * (v - d)))) ≤ T d / D := by
    apply (div_le_div_iff₀ he hD).mpr
    linarith only [hw]
  exact ⟨hD, hM, hmean, hRlower, hRupper⟩

/-- The actual radical contribution has strictly negative mixed derivative in the
independent coordinates on the central strip at gap four. -/
theorem separatedFour_radical_mixed_neg {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 1 / 2 ≤ u) (hu₄ : u ≤ 4) (hd : 4 ≤ v - u) :
    deriv (fun y ↦ deriv (fun x ↦ separatedGapRadicalContribution p x y) u) v < 0 := by
  let h : ℝ := 3 / (p : ℝ)
  let c := (3 + h) * (3 + 2 * h) / 2
  let scale : ℝ := h * Real.sqrt (((p + 2).choose 2 : ℝ) / (p + 1)) / (2 * c)
  let d := v - u
  let z := upperTailRadicalRoot h
  let T := deriv z
  let rho (s : ℝ) := deriv T s / T s
  let P := radicalLeftFactor p
  let Q := radicalUpperFactor p h
  let J := radicalGapFactor h
  let L := upperTailSlope h
  let j (s : ℝ) := 3 / 2 - L s
  let D (y : ℝ) := z y - z (y - u)
  let M := T v - T d
  let q := L d * (h + L d)
  let C (s : ℝ) := compositionMoment p 0 (-s)
  let α := 1 / 2 - (deriv C u / C u) / 2
  let b := 1 + 2 / (Real.exp u - 1) - (deriv C u / C u) / 2
  have hu₀ : 0 < u := by linarith only [hu]
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hp₁ : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp₁
  change 4 ≤ d at hd
  have hvdu : v = d + u := by dsimp [d]; ring
  have hvd : v - d = u := by dsimp [d]; ring
  have hdv : d < v := by linarith only [hvdu, hu₀]
  have hv : 1 ≤ v := by linarith only [hvdu, hu₀, hd]
  have hd₀ : 0 < d := by linarith only [hd]
  have hv₀ : 0 < v := hd₀.trans hdv
  have hscale : 0 < scale := by
    have hN : 0 < ((p + 2).choose 2 : ℝ) := by
      exact_mod_cast Nat.choose_pos (show 2 ≤ p + 2 by omega)
    dsimp only [scale, c]
    positivity
  have hz (s : ℝ) (hs : 0 < s) : HasDerivAt z (T s) s :=
    (hasDerivAt_upperTailRadicalRoot hh hs).differentiableAt.hasDerivAt
  obtain ⟨hP, hPd⟩ := radicalLeftFactor_jet hp₀ hu₀
  obtain ⟨hQ, β, hβ, hQd⟩ := radicalUpperFactor_jet hp₀ hv
  obtain ⟨hJ, hJd⟩ := radicalGapFactor_jet hh hd₀
  change HasDerivAt P (P u * α) u at hPd
  change HasDerivAt Q (Q v * β) v at hQd
  change HasDerivAt J (J d * j d) d at hJd
  obtain ⟨hT, hTd, _, _⟩ := separatedFour_radical_logDeriv_bounds hh hhmax hd
  obtain ⟨hD, hM, hmid, hRlower, hRupper⟩ := radical_dividedDifference_bounds hh hhmax hd hdv
  let R := T d / D v
  let U := α - j d + 2 * R
  let V := β + j d + 2 * (M / D v)
  change 0 < D v at hD
  change M / D v ≤ -(17 / 12 : ℝ) at hM
  change rho d - M / D v ≤ 3 * (v - d) / (d * (d + v)) at hmid
  change (17 / 12) / (1 - Real.exp (-((17 / 12) * (v - d)))) ≤ R at hRlower
  change R ≤ 1 / (v - d) + 41 / 20 at hRupper
  rw [hvd] at hmid hRlower hRupper
  have hL := (upperTailSlope_bounds hh hd₀).1
  have hj : j d ≤ 3 / 2 := by dsimp only [j]; linarith only [hL]
  have hq : 0 ≤ q := mul_nonneg hL.le (add_nonneg hh.le hL.le)
  have hb : 12 / 25 ≤ b := (separatedGap_lowerSlope_bounds hp₀ hu₀ hu₄).1
  have hbdef : b = α + 1 / 2 + 2 / (Real.exp u - 1) := by dsimp only [b, α]; ring
  have hU : 269 / 300 ≤ U := by
    have hratio :=
      (scaled_exponential_ratio_lower hu₀ (by norm_num : (1 : ℝ) ≤ 17 / 12)).trans hRlower
    have he₀ := (Real.exp_pos u).ne'
    have he₁ := (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu₀))).ne'
    have he₂ := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu₀)).ne'
    have he : 1 / (1 - Real.exp (-u)) = 1 + 1 / (Real.exp u - 1) := by
      rw [Real.exp_neg] at he₁ ⊢
      field_simp [he₀, he₁, he₂]
      ring
    rw [he] at hratio
    simp only [div_eq_mul_inv] at hratio hbdef
    dsimp only [U]
    linarith only [hratio, hj, hb, hbdef]
  have hV : V ≤ -(4 / 3 : ℝ) := by dsimp only [V]; linarith only [hβ, hj, hM]
  have hUV : U * V ≤ (269 / 300) * (-(4 / 3 : ℝ)) := calc
    _ ≤ U * (-(4 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hV (by linarith only [hU])
    _ ≤ _ := mul_le_mul_of_nonpos_right hU (by norm_num)
  have herror : 2 * R * (rho d - M / D v) ≤ 23 / 20 := by
    have hR : 0 ≤ R := div_nonneg hT.le hD.le
    have hden : 0 < d * (d + v) := mul_pos hd₀ (add_pos hd₀ hv₀)
    have hRu := mul_le_mul_of_nonneg_right hRupper hu₀.le
    rw [add_mul, one_div_mul_cancel hu₀.ne'] at hRu
    have hdv' : 4 * (8 + u) ≤ d * (d + v) :=
      mul_le_mul hd (by linarith only [hvdu, hd]) (by linarith only [hu₀]) hd₀.le
    have hcap : 6 * (1 + (41 / 20) * u) ≤ (23 / 20) * (d * (d + v)) := calc
      _ ≤ (23 / 20) * (4 * (8 + u)) := by linarith only [hu₄]
      _ ≤ _ := mul_le_mul_of_nonneg_left hdv' (by norm_num)
    calc
      _ ≤ (2 * R) * (3 * u / (d * (d + v))) := mul_le_mul_of_nonneg_left hmid (by positivity)
      _ = 6 * (R * u) / (d * (d + v)) := by ring
      _ ≤ _ := (div_le_iff₀ hden).mpr
        ((mul_le_mul_of_nonneg_left hRu (by norm_num : (0 : ℝ) ≤ 6)).trans hcap)
  have hsign : U * V - q + 2 * R * (rho d - M / D v) < 0 := by
    have hmargin : U * V - q + 2 * R * (rho d - M / D v) ≤ -(41 / 900 : ℝ) := by
      linarith only [hUV, hq, herror]
    exact hmargin.trans_lt (by norm_num)
  have hformula (y : ℝ) (hy : 0 < y-u) :
      deriv (fun x ↦ separatedGapRadicalContribution p x y) u =
        scale*(P u*Q y*J (y-u)*
          ((D y)^2*(α-j (y-u))+2*D y*T (y-u))) := by
    have hynear : ∀ᶠ x in 𝓝 u, 0 < y-x :=
      ((continuous_const.sub continuous_id).continuousAt :
        ContinuousAt (fun x : ℝ ↦ y-x) u).eventually (eventually_gt_nhds hy)
    have heq : (fun x ↦ separatedGapRadicalContribution p x y) =ᶠ[𝓝 u]
        (fun x ↦ scale*radicalFactorization p h x y) := by
      filter_upwards [eventually_gt_nhds hu₀, hynear] with x hx hxy
      exact separatedGapRadicalContribution_eq hp₀ hx hxy
    have hd' : HasDerivAt (fun x : ℝ ↦ y-x) (-1) u := by
      simpa only [zero_sub] using (hasDerivAt_id' u).const_sub y
    have hJ' := ((radicalGapFactor_jet hh hy).2).comp u hd'
    change HasDerivAt (fun x ↦ J (y-x)) ((J (y-u)*j (y-u))*(-1)) u at hJ'
    have hZ' := ((hz (y-u) hy).comp u hd').const_sub (z y)
    change HasDerivAt (fun x ↦ z y-z (y-x)) (-(T (y-u)*(-1))) u at hZ'
    have hder := (((hPd.mul_const (Q y)).mul hJ').mul (hZ'.pow 2)).const_mul scale
    change HasDerivAt (fun x ↦ scale*radicalFactorization p h x y) _ u at hder
    rw [heq.deriv_eq, hder.deriv]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.mul_apply, Pi.pow_apply]
    change _ = scale*(P u*Q y*J (y-u)*((z y-z (y-u))^2*(α-j (y-u))+
      2*(z y-z (y-u))*T (y-u)))
    ring
  have hlocal : (fun y ↦ deriv (fun x ↦ separatedGapRadicalContribution p x y) u) =ᶠ[𝓝 v]
      (fun y ↦ scale*(P u*Q y*J (y-u)*((D y)^2*(α-j (y-u))+2*D y*T (y-u)))) := by
    have hpos : ∀ᶠ y in 𝓝 v, 0 < y-u :=
      ((continuous_id.sub continuous_const).continuousAt :
        ContinuousAt (fun y : ℝ ↦ y-u) v).eventually (eventually_gt_nhds hd₀)
    exact hpos.mono hformula
  have hg : HasDerivAt (fun y : ℝ ↦ y-u) 1 v := (hasDerivAt_id' v).sub_const u
  have hD' : HasDerivAt D M v := by
    have hdif := (hz v hv₀).sub ((hz d hd₀).comp v hg)
    change HasDerivAt D (T v-T d*1) v at hdif
    simpa only [M, mul_one] using hdif
  have hj' : HasDerivAt (fun y ↦ α-j (y-u)) (-q) v := by
    have hl := ((hasDerivAt_upperTailSlope hh hd₀).comp v hg).const_sub (3/2 : ℝ)
    have hdif := hl.const_sub α
    change HasDerivAt (fun y ↦ α-j (y-u)) (-(-(-q*1))) v at hdif
    simpa only [mul_one, neg_neg] using hdif
  have hT' : HasDerivAt (fun y ↦ T (y-u)) (T d*rho d) v := by
    have ht := hTd.hasDerivAt.congr_deriv (show deriv T d = T d*rho d by
      dsimp [rho]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hT.ne'])
    have hdif := ht.comp v hg
    change HasDerivAt (fun y ↦ T (y-u)) (T d*rho d*1) v at hdif
    simpa only [mul_one] using hdif
  have hJ' := hJd.comp v hg
  change HasDerivAt (fun y ↦ J (y-u)) (J d*j d*1) v at hJ'
  have hleft := (hQd.const_mul (P u)).mul hJ'
  have hright := ((hD'.pow 2).mul hj').add ((hD'.const_mul 2).mul hT')
  have hder := (hleft.mul hright).const_mul scale
  change HasDerivAt (fun y ↦ scale*(P u*Q y*J (y-u)*
    ((D y)^2*(α-j (y-u))+2*D y*T (y-u)))) _ v at hder
  rw [hlocal.deriv_eq, hder.deriv]
  calc
    _ = scale*(P u*Q v*J d*(D v)^2)*(U*V-q+2*R*(rho d-M/D v)) := by
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, Pi.mul_apply, Pi.add_apply,
        Pi.pow_apply]
      change scale*((P u*(Q v*β)*J d + P u*Q v*(J d*j d))*
        ((D v)^2*(α-j d)+2*D v*T d) + P u*Q v*J d*
        (2*D v*M*(α-j d)+(D v)^2*(-q)+(2*M*T d+2*D v*(T d*rho d)))) = _
      dsimp only [U, V, R]
      field_simp [hD.ne']
      ring
    _ < 0 := mul_neg_of_pos_of_neg (mul_pos hscale
      (mul_pos (mul_pos (mul_pos hP hQ) hJ) (sq_pos_of_pos hD))) hsign

#print axioms separatedFour_radical_logDeriv_bounds
#print axioms separatedFour_radical_mixed_neg

end RefinedBMV.PositiveCenter
