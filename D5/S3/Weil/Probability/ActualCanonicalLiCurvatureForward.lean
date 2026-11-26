/- GID: D5/S3/Weil/Probability/ActualCanonicalLiCurvatureForward
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/ActualCanonicalLiCurvatureForward
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gram sums of actual positive zero pairs give the canonical Li curvature criterion. -/

import D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent
import D5.S3.Weil.Probability.CanonicalLiCurvatureZeroFree
import Mathlib.Analysis.Matrix.Order

/-! The derivative-defined Li curvature is the moment sequence of the
normalized actual zero pairs on the critical line. Finite Gram sums converge
entrywise to its Toeplitz matrices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward

open Complex Filter Matrix
open scoped Topology ComplexConjugate ComplexOrder BigOperators
open ActualCanonicalLiForwardPairedResolvent
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.ActualZeroGeometry
open D5.S3.Weil.Probability.CanonicalLiDiskEquivalence
open D5.S3.Zeros.Endpoints.CanonicalLiLocalExpansion
open D5.S3.Weil.Probability.CanonicalLiCurvatureZeroFree
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion

private theorem ratio_norm (hRH : RiemannHypothesis) (i : ℕ) : ‖zeroRatio i‖ = 1 :=
  rh_iff_nontrivial_zero_cayley_norm.mp hRH _ (zetaZeroData_isNontrivial i)

private theorem ratio_mul_conj (hRH : RiemannHypothesis) (i : ℕ) :
    zeroRatio i * conj (zeroRatio i) = 1 := by
  rw [Complex.mul_conj', ratio_norm hRH i]
  norm_num

private theorem pairCoefficient_ofReal (n i : ℕ) (hi : 0 < (zetaZeroData.gamma i).re) :
    (pairCoefficient n i : ℂ) = (zetaZeroData.multiplicity i : ℂ) *
      (2 - (zeroRatio i) ^ n - (conj (zeroRatio i)) ^ n) := by
  rw [pairCoefficient, ite_eq_left hi, ← map_pow (starRingEnd ℂ)]
  apply Complex.ext <;>
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat,
      Complex.ofReal_one, Complex.ofReal_natCast, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.natCast_re, Complex.natCast_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im] <;> norm_num
  ring

/-- Exact second difference of every actual zero-pair contribution. -/
private theorem pairCoefficient_second_difference (hRH : RiemannHypothesis) (n i : ℕ) :
    ((pairCoefficient (n + 2) i - 2 * pairCoefficient (n + 1) i + pairCoefficient n i : ℝ) : ℂ) =
      (pairCoefficient 1 i : ℂ) * ((zeroRatio i) ^ (n + 1) + (conj (zeroRatio i)) ^ (n + 1)) := by
  classical
  by_cases hi : 0 < (zetaZeroData.gamma i).re
  · push_cast
    rw [pairCoefficient_ofReal _ _ hi, pairCoefficient_ofReal _ _ hi,
      pairCoefficient_ofReal _ _ hi, pairCoefficient_ofReal _ _ hi]
    simp only [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    linear_combination (zetaZeroData.multiplicity i : ℂ) *
      ((zeroRatio i) ^ n + (conj (zeroRatio i)) ^ n) * ratio_mul_conj hRH i
  · simp [pairCoefficient, hi]

/-- The positive real mass assigned to each of the two members of a pair. -/
private def pairMass (i : ℕ) : ℝ := pairCoefficient 1 i / (2 * canonicalLiCoefficient 1)

private theorem pairMass_pos (i : ℕ) (hi : 0 < (zetaZeroData.gamma i).re) :
    0 < pairMass i := by
  apply div_pos _ (mul_pos (by norm_num) canonical_li_one_pos)
  have hre : 0 < (zetaZeroData.zero i).re := (zetaZeroData_isNontrivial i).2.1
  rw [pairCoefficient, ite_eq_left hi, pow_one, zeroRatio, Complex.sub_re,
    Complex.one_re, one_div, Complex.inv_re, sub_sub_cancel]
  exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (zetaZeroData_multiplicity_pos i)))
    (div_pos hre (Complex.normSq_pos.mpr (fun hz => by simp [hz] at hre)))

private theorem pairMass_nonneg (i : ℕ) : 0 ≤ pairMass i := by
  by_cases hi : 0 < (zetaZeroData.gamma i).re
  · exact (pairMass_pos i hi).le
  · simp [pairMass, pairCoefficient, hi]

private theorem pair_hasSum (n : ℕ) :
    HasSum (fun i : ℕ => (pairCoefficient n i : ℂ)) (pairSum n : ℂ) :=
  Complex.hasSum_ofReal.mpr (pairCoefficient_abs_summable n).of_abs.hasSum

/-- The actual probability moment expansion of the normalized curvature at
all integer orders, including its zeroth value. -/
private theorem canonicalCurvature_actual_pair_hasSum
    (halfFree : ∀ s : ℂ, (1 : ℝ) / 2 < s.re → xiReading s ≠ 0)
    (k : ℤ) :
    HasSum (fun i : ℕ => (pairMass i : ℂ) *
      ((zeroRatio i) ^ k.natAbs + (conj (zeroRatio i)) ^ k.natAbs))
      (canonicalLiCurvature k) := by
  have hRH := rh_iff_xi_right_half_plane.mpr halfFree
  by_cases hzero : k = 0
  · subst k
    have hv : (2 / (2 * (canonicalLiCoefficient 1 : ℂ))) * (pairSum 1 : ℂ) = 1 := by
      rw [← canonicalLiCoefficient_eq_actual_pairSum 1 (.inr halfFree)]
      have hn : (canonicalLiCoefficient 1 : ℂ) ≠ 0 := by
        exact_mod_cast canonical_li_one_pos.ne'
      field_simp
    have h := (pair_hasSum 1).mul_left (2 / (2 * (canonicalLiCoefficient 1 : ℂ)))
    rw [hv] at h
    rw [canonical_li_curvature_zero]
    apply h.congr_fun
    intro i
    simp [pairMass]
    ring
  · let n := k.natAbs - 1
    have hn : n + 1 = k.natAbs := by
      have hk : k.natAbs ≠ 0 := by simpa using hzero
      dsimp [n]
      omega
    have hn2 : n + 2 = k.natAbs + 1 := by omega
    have h := (((pair_hasSum (n + 2)).sub ((pair_hasSum (n + 1)).mul_left (2 : ℂ))).add
      (pair_hasSum n)).div_const (2 * (canonicalLiCoefficient 1 : ℂ))
    have hvalue : ((pairSum (n + 2) : ℂ) - 2 * (pairSum (n + 1) : ℂ) + (pairSum n : ℂ)) /
          (2 * (canonicalLiCoefficient 1 : ℂ)) = canonicalLiCurvature k := by
      rw [← canonicalLiCoefficient_eq_actual_pairSum (n + 2) (.inr halfFree),
        ← canonicalLiCoefficient_eq_actual_pairSum (n + 1) (.inr halfFree),
        ← canonicalLiCoefficient_eq_actual_pairSum n (.inr halfFree)]
      rw [canonicalLiCurvature, ite_eq_right hzero, hn, hn2]
      simp [n]
    rw [hvalue] at h
    apply h.congr_fun
    intro i
    have hp := pairCoefficient_second_difference hRH n i
    push_cast at hp
    rw [hp, hn]
    simp [pairMass]
    ring

private theorem symmetric_powers_difference (a : ℂ) (hu : a * conj a = 1) (j k : ℕ) :
    a ^ j * (conj a) ^ k + (conj a) ^ j * a ^ k =
      a ^ ((j : ℤ) - (k : ℤ)).natAbs + (conj a) ^ ((j : ℤ) - (k : ℤ)).natAbs := by
  have hle {u v : ℕ} (h : v ≤ u) :
      a ^ u * (conj a) ^ v + (conj a) ^ u * a ^ v = a ^ (u - v) + (conj a) ^ (u - v) := by
    have hpow : a ^ v * (conj a) ^ v = 1 := by rw [← mul_pow, hu, one_pow]
    conv_lhs => rw [show u = (u - v) + v by omega, pow_add, pow_add]
    calc
      _ = a ^ (u - v) * (a ^ v * (conj a) ^ v) +
          (conj a) ^ (u - v) * (a ^ v * (conj a) ^ v) := by ring
      _ = _ := by rw [hpow, mul_one, mul_one]
  by_cases h : k ≤ j
  · rw [show (j : ℤ) - (k : ℤ) = ((j - k : ℕ) : ℤ) by omega, Int.natAbs_natCast]
    exact hle h
  · have h' : j ≤ k := by omega
    rw [show (j : ℤ) - (k : ℤ) = -((k - j : ℕ) : ℤ) by omega,
      Int.natAbs_neg, Int.natAbs_natCast]
    calc
      _ = a ^ k * (conj a) ^ j + (conj a) ^ k * a ^ j := by ring
      _ = _ := hle h'

private def firstPairVector (N i : ℕ) : Fin (N + 1) → ℂ :=
  fun j => (Real.sqrt (pairMass i) : ℂ) * (zeroRatio i) ^ j.val

private def secondPairVector (N i : ℕ) : Fin (N + 1) → ℂ :=
  fun j => (Real.sqrt (pairMass i) : ℂ) * (conj (zeroRatio i)) ^ j.val

private def pairMatrix (N i : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  vecMulVec (firstPairVector N i) (star (firstPairVector N i)) +
    vecMulVec (secondPairVector N i) (star (secondPairVector N i))

private theorem pairMatrix_psd (N i : ℕ) : (pairMatrix N i).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star (firstPairVector N i)).add
    (Matrix.posSemidef_vecMulVec_self_star (secondPairVector N i))

private theorem pairMatrix_entry (hRH : RiemannHypothesis) (N i : ℕ)
    (j k : Fin (N + 1)) : pairMatrix N i j k = (pairMass i : ℂ) *
      ((zeroRatio i) ^ ((j.val : ℤ) - (k.val : ℤ)).natAbs +
        (conj (zeroRatio i)) ^ ((j.val : ℤ) - (k.val : ℤ)).natAbs) := by
  have hs : (Real.sqrt (pairMass i) : ℂ) ^ 2 = (pairMass i : ℂ) := by
    exact_mod_cast Real.sq_sqrt (pairMass_nonneg i)
  simp only [pairMatrix, Matrix.add_apply, Matrix.vecMulVec_apply,
    firstPairVector, secondPairVector, Pi.star_apply, Complex.star_def,
    map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj]
  calc
    _ = (Real.sqrt (pairMass i) : ℂ) ^ 2 *
        ((zeroRatio i) ^ j.val * (conj (zeroRatio i)) ^ k.val +
          (conj (zeroRatio i)) ^ j.val * (zeroRatio i) ^ k.val) := by ring
    _ = _ := by rw [hs, symmetric_powers_difference _ (ratio_mul_conj hRH i)]

private theorem curvature_posSemidef_of_halfFree
    (halfFree : ∀ s : ℂ, (1 : ℝ) / 2 < s.re → xiReading s ≠ 0)
    (N : ℕ) : (toeplitzMatrix canonicalLiCurvature N).PosSemidef := by
  have hRH := rh_iff_xi_right_half_plane.mpr halfFree
  have hlim : Tendsto (fun M : ℕ => ∑ i ∈ Finset.range M, pairMatrix N i)
      atTop (𝓝 (toeplitzMatrix canonicalLiCurvature N)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_pi_nhds.mpr
    intro k
    have hs := canonicalCurvature_actual_pair_hasSum halfFree ((j.val : ℤ) - (k.val : ℤ))
    simpa [Matrix.sum_apply, toeplitzMatrix, pairMatrix_entry hRH] using hs.tendsto_sum_nat
  exact Matrix.posSemidef_is_closed.mem_of_tendsto hlim
    (Filter.Eventually.of_forall fun M => Matrix.posSemidef_sum _ fun i _ => pairMatrix_psd N i)

/-- The zeroth Toeplitz order is positive semidefinite, and under actual xi
right-half-plane nonvanishing every order is positive semidefinite. -/
theorem canonical_curvature_forward_posSemidef (N : ℕ)
    (h : N = 0 ∨ ∀ s : ℂ, (1 : ℝ) / 2 < s.re → xiReading s ≠ 0) :
    (toeplitzMatrix canonicalLiCurvature N).PosSemidef := by
  rcases h with rfl | halfFree
  · have hzero : toeplitzMatrix canonicalLiCurvature 0 = 1 := by
      ext j k
      have hjk : j = k := Fin.ext (by omega)
      simp [hjk, toeplitzMatrix, Matrix.one_apply]
    rw [hzero]
    exact Matrix.PosSemidef.one
  · exact curvature_posSemidef_of_halfFree halfFree N

/-- RH is equivalent to positivity of every actual normalized Li curvature
Toeplitz matrix. -/
theorem rh_iff_canonical_curvature_posSemidef :
    RiemannHypothesis ↔ ∀ N : ℕ, (toeplitzMatrix canonicalLiCurvature N).PosSemidef :=
  ⟨fun hRH N => canonical_curvature_forward_posSemidef N
      (.inr (rh_iff_xi_right_half_plane.mp hRH)),
    canonical_curvature_posSemidef_implies_rh⟩

#print axioms canonical_curvature_forward_posSemidef
#print axioms rh_iff_canonical_curvature_posSemidef

end D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward
