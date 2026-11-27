/- GID: D5/S3/Quantum/Semigroups/WuCubicMassCancellation
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicMassCancellation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict increase of the conditioned Wu cubic deficit from joint entropy and mass control. -/

import D5.S3.Quantum.Semigroups.WuCubicConditionedTranslation
import D5.S3.Quantum.Divergence.GibbsCubicMassCancellation
import D5.S3.Quantum.Divergence.GibbsCubicCorrectionBound

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicMassCancellation

open WuCubicOperatorBridge (D Mat Occupation)
open WuCubicOperatorNormalization (operatorDeficit)
open WuCubicTranslationEnergy (base baseEntry sandwich translate cubicEnergy V V₁ pairWeight
  V_eq_entries cubicEnergy_hasDerivAt_degree cubicEnergy_deriv_ge)
open WuCubicConditionedTranslation (Conditioned embedded bmin bmax bmin_pos bmax_div_bmin)
open WuRepeatedMiddleCubic (alpha)
open D5.S3.Quantum.Divergence.GibbsCubicTranslationEntropy (cubicEntropy correction spectralRatio)
open D5.S3.Quantum.Divergence.GibbsCubicMassCancellation
  (hasDerivAt_cubicEntropy_centered deriv_cubicEntropy_div_three_le)
open D5.S3.Quantum.Divergence.GibbsCubicCorrectionBound (correction_le_weighted_trace)
open private operatorDeficit_translate_eq base_posDef base_bounds base_cube_trace base_center
  thermal_trace_square_ge spectral_min_mul_trace_square_le posDef_of_spectral_bounds from
  D5.S3.Quantum.Semigroups.WuCubicConditionedTranslation
open private baseEntry_pos sandwich_hermitian from D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy

private theorem variance_pos {r : ℝ} (hr : 1 ≤ r) {A : Mat}
    (hA : A.IsHermitian) (hA0 : A ≠ 0) : 0 < V r A := by
  have hweight (i j : Occupation) : 0 < pairWeight r i j := by
    unfold pairWeight
    exact div_pos (mul_pos (mul_pos (baseEntry_pos hr i) (baseEntry_pos hr j))
      (add_pos (baseEntry_pos hr i) (baseEntry_pos hr j))) (by norm_num)
  have hentry : ∃ i j, A i j ≠ 0 := by
    by_contra! hzero
    exact hA0 (Matrix.ext fun i j => hzero i j)
  obtain ⟨i, j, hij⟩ := hentry
  have hnorm : Complex.normSq (A i j) ≠ 0 := fun hz => hij (Complex.normSq_eq_zero.mp hz)
  have hterm (k l : Occupation) : 0 ≤ pairWeight r k l * Complex.normSq (A k l) :=
    mul_nonneg (hweight k l).le (Complex.normSq_nonneg _)
  rw [V_eq_entries r A hA]
  refine Finset.sum_pos' (fun k _ => Finset.sum_nonneg fun l _ => hterm k l)
    ⟨i, Finset.mem_univ _, ?_⟩
  exact Finset.sum_pos' (fun l _ => hterm i l) ⟨j, Finset.mem_univ _,
    mul_pos (hweight i j) (lt_of_le_of_ne (Complex.normSq_nonneg _) hnorm.symm)⟩

private theorem spectral_upper_div_bmin_le {r t mmin mmax : ℝ} {A : Mat}
    (hr : 1 ≤ r) (hr₁ : r ≤ 6 / 5) (hcenter : (D r * A).trace = 0)
    (hmmax : 0 < mmax) (hmin : (2 / 3 : ℝ) * mmax ≤ mmin)
    (hM : (embedded r A t).IsHermitian) (hlower : ∀ j, mmin ≤ hM.eigenvalues j) :
    mmax / bmin r ≤ (15 / 8 : ℝ) * t := by
  have hb := bmin_pos hr
  have hthermal := thermal_trace_square_ge hr hr₁
  have hmean := spectral_min_mul_trace_square_le hr hcenter hM hlower
  have htrace : 0 ≤ (base r ^ 2).trace.re := by
    by_contra! h
    exact (not_lt_of_ge ((by norm_num : (0 : ℝ) ≤ 4 / 5).trans hthermal))
      (mul_neg_of_pos_of_neg hb h)
  have hscaled : (4 / 5 : ℝ) * ((2 / 3 : ℝ) * mmax) ≤ t * bmin r := by
    calc
      _ ≤ (bmin r * (base r ^ 2).trace.re) * ((2 / 3 : ℝ) * mmax) :=
        mul_le_mul_of_nonneg_right hthermal (by positivity)
      _ = ((2 / 3 : ℝ) * mmax * (base r ^ 2).trace.re) * bmin r := by ring
      _ ≤ (mmin * (base r ^ 2).trace.re) * bmin r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmin htrace) hb.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hmean hb.le
  apply (div_le_iff₀ hb).mpr
  linarith only [hscaled]

private theorem correction_le {r t : ℝ} {A : Mat} (hr : 1 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hA : A.IsHermitian) (hV : 0 ≤ V r A) (hbounds : bmin r ≤ bmax r)
    (hκ : bmax r ≤ (36 / 25 : ℝ) * bmin r) :
    correction (base r) (embedded r A t) ≤ (22 / 305 : ℝ) * V r A := by
  have hb := bmin_pos hr
  have hspread : (bmax r - bmin r) / (bmax r + bmin r) ≤ (11 / 61 : ℝ) :=
    (div_le_iff₀ (add_pos (hb.trans_le hbounds) hb)).mpr (by linarith only [hκ])
  have hlog : Real.log (bmax r / bmin r) ≤ (2 / 5 : ℝ) := by
    calc
      _ = 2 * Real.log r := by rw [bmax_div_bmin hr, Real.log_pow, Nat.cast_ofNat]
      _ ≤ _ := by linarith only [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hr), hr₁]
  have hlog0 : 0 ≤ Real.log (bmax r / bmin r) :=
    Real.log_nonneg ((le_div_iff₀ hb).mpr (by simpa only [one_mul] using hbounds))
  have hcoeff : (bmax r - bmin r) / (bmax r + bmin r) * Real.log (bmax r / bmin r) ≤
      (22 / 305 : ℝ) := by
    calc
      _ ≤ (11 / 61 : ℝ) * (2 / 5 : ℝ) := mul_le_mul hspread hlog hlog0 (by norm_num)
      _ = _ := by norm_num
  have hcorr := correction_le_weighted_trace (base r) (sandwich r A) (base_posDef hr)
    (sandwich_hermitian r A hA) t hb (base_bounds hr)
  exact hcorr.trans (mul_le_mul_of_nonneg_right hcoeff hV)

/-- The literal Wu cubic deficit has positive derivative along a positive,
conditioned translation of a nonzero centered direction with degree-one mass at most
`17/25` of its variance. This includes the tracial temperature and the degree boundary. -/
theorem operatorDeficit_deriv_pos_of_degree_one_le {r t : ℝ} {A : Mat}
    (hr : 1 ≤ r) (hr₁ : r ≤ 6 / 5) (ht : 0 < t)
    (hA : A.IsHermitian) (hcenter : (D r * A).trace = 0) (hA0 : A ≠ 0)
    (hcond : Conditioned (embedded r A t)) (hdegree : V₁ r A ≤ (17 / 25 : ℝ) * V r A) :
    0 < deriv (fun s : ℝ => operatorDeficit r (translate A s)) t := by
  obtain ⟨hHerm, mmin, mmax, hmmax, hρ, hbounds⟩ := hcond
  let hB := base_posDef hr
  have hM : (t • base r + sandwich r A).PosDef :=
    posDef_of_spectral_bounds hHerm hmmax hρ hbounds
  have hb := bmin_pos hr
  have hthermalEntry := base_bounds hr (0, 0)
  have hthermalOrder : bmin r ≤ bmax r := hthermalEntry.1.trans hthermalEntry.2
  have hbmax := hb.trans_le hthermalOrder
  have hκ : bmax r ≤ (36 / 25 : ℝ) * bmin r := by
    apply (div_le_iff₀ hb).mp
    rw [bmax_div_bmin hr]
    exact (pow_le_pow_left₀ (zero_le_one.trans hr) hr₁ 2).trans (by norm_num)
  have hmin := (le_div_iff₀ hmmax).mp hρ
  have hmmin : 0 < mmin := (mul_pos (by norm_num : (0 : ℝ) < 2 / 3) hmmax).trans_le hmin
  have hwidth : mmax / bmin r / t ≤ (54 / 25 : ℝ) * (mmin / bmax r / t) := by
    have hratio : mmax / bmin r ≤ (54 / 25 : ℝ) * (mmin / bmax r) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hb hbmax]
      calc
        _ ≤ ((3 / 2 : ℝ) * mmin) * ((36 / 25 : ℝ) * bmin r) :=
          mul_le_mul (by linarith only [hmin]) hκ hbmax.le (by positivity)
        _ = _ := by ring
    calc
      _ ≤ ((54 / 25 : ℝ) * (mmin / bmax r)) / t := div_le_div_of_nonneg_right hratio ht.le
      _ = _ := mul_div_assoc _ _ _
  have hinterval (q : Occupation × Occupation) :
      mmin / bmax r / t ≤ spectralRatio hB.isHermitian hM.isHermitian q / t ∧
        spectralRatio hB.isHermitian hM.isHermitian q / t ≤ mmax / bmin r / t := by
    have hbi := base_bounds hr q.1
    have hbi₀ := hB.eigenvalues_pos q.1
    have hmi := hbounds q.2
    unfold spectralRatio
    constructor
    · exact div_le_div_of_nonneg_right
        ((div_le_div_of_nonneg_left hmmin.le hbi₀ hbi.2).trans
          (div_le_div_of_nonneg_right hmi.1 hbi₀.le)) ht.le
    · exact div_le_div_of_nonneg_right
        ((div_le_div_of_nonneg_right hmi.2 hbi₀.le).trans
          (div_le_div_of_nonneg_left hmmax.le hb hbi.1)) ht.le
  have hupper := spectral_upper_div_bmin_le hr hr₁ hcenter hmmax hmin hHerm (fun j => (hbounds j).1)
  have hcap (q : Occupation × Occupation) :
      spectralRatio hB.isHermitian hM.isHermitian q / t ≤ 15 / 8 :=
    (hinterval q).2.trans ((div_le_iff₀ ht).mpr hupper)
  let F : ℝ → ℝ := fun s => cubicEntropy (base r) (embedded r A s)
  have hF : HasDerivAt F (deriv F t) t := by
    have h := hasDerivAt_cubicEntropy_centered (base r) (sandwich r A) ht hB hM
      (base_cube_trace hr) (base_center hr hcenter)
    dsimp only at h
    simpa only [F, embedded] using h.congr_deriv h.deriv.symm
  have hentropy := deriv_cubicEntropy_div_three_le (base r) (sandwich r A) ht hB hM
    (base_cube_trace hr) (base_center hr hcenter) (div_pos (div_pos hmmin hbmax) ht) hwidth hinterval hcap
  change deriv F t / 3 ≤ (61 / 32 : ℝ) * V r A + correction (base r) (embedded r A t) at hentropy
  have hV := variance_pos hr hA hA0
  have hcorr := correction_le (t := t) hr hr₁ hA hV.le hthermalOrder hκ
  have hFupper : deriv F t ≤ 3 * (((61 / 32 : ℝ) + 22 / 305) * V r A) := by
    linarith only [hentropy, hcorr]
  have hα := WuCubicOccupationTaylor.alpha_bounds_of_one_le hr
  have hcost : alpha r * deriv F t ≤ (3 / 2 : ℝ) * ((61 / 32 : ℝ) + 22 / 305) * V r A := by
    calc
      _ ≤ alpha r * (3 * (((61 / 32 : ℝ) + 22 / 305) * V r A)) :=
        mul_le_mul_of_nonneg_left hFupper hα.1
      _ ≤ (1 / 2 : ℝ) * (3 * (((61 / 32 : ℝ) + 22 / 305) * V r A)) :=
        mul_le_mul_of_nonneg_right hα.2 (by positivity)
      _ = _ := by ring
  have hE := cubicEnergy_hasDerivAt_degree hr A hA t
  have henergy : (297 / 100 : ℝ) * V r A ≤ deriv (fun s : ℝ => cubicEnergy r (translate A s)) t := by
    calc
      _ ≤ (9 / 4 : ℝ) * (2 * V r A - V₁ r A) := by linarith only [hdegree]
      _ ≤ _ := cubicEnergy_deriv_ge hr A hA hcenter t
  have hdeficit : HasDerivAt (fun s : ℝ => operatorDeficit r (translate A s))
      (deriv (fun s : ℝ => cubicEnergy r (translate A s)) t - alpha r * deriv F t) t := by
    simp_rw [operatorDeficit_translate_eq hr]
    exact (hE.congr_deriv hE.deriv.symm).sub (hF.const_mul (alpha r))
  rw [hdeficit.deriv]
  have hmargin : 0 < ((297 / 100 : ℝ) - (3 / 2 : ℝ) * (61 / 32 + 22 / 305)) * V r A :=
    mul_pos (by norm_num) hV
  linarith only [henergy, hcost, hmargin]

end D5.S3.Quantum.Semigroups.WuCubicMassCancellation
