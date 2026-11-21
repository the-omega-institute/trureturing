/- GID: D5/S3/Quantum/Analysis/RefinedBMV33
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV33
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite-dimensional refined BMV product bound follows from positive closed-walk Schur forms. -/

import D5.S3.Quantum.Analysis.RefinedBMVKernel
import D5.S3.Quantum.Analysis.RefinedBMVWords
import D5.S3.Weil.Probability.FiniteGaussianSchoenberg

open Matrix
open scoped ComplexOrder BigOperators

noncomputable section

namespace RefinedBMV

variable {n : Type*} [Fintype n] [DecidableEq n]

def walk (B : Matrix n n ℂ) : (n → n → n → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ i, ∑ j, ∑ k, B i j * B j k * B k i * f i j k
  map_add' f g := by simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem walk_rotate (B : Matrix n n ℂ) (f : n → n → n → ℂ) :
    walk B (fun i j k ↦ f j k i) = walk B f := by
  change (∑ i, ∑ j, ∑ k, B i j * B j k * B k i * f j k i) =
    ∑ i, ∑ j, ∑ k, B i j * B j k * B k i * f i j k
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

private theorem trace_diagonal_walk (B : Matrix n n ℂ) (u v w : n → ℂ) :
    trace (diagonal u * (B * (diagonal v * (B * (diagonal w * B))))) =
      walk B (fun i j k ↦ u i * v j * w k) := by
  change _ = ∑ i, ∑ j, ∑ k, B i j * B j k * B k i * (u i * v j * w k)
  simp only [trace, diag_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [diagonal_mul, mul_apply]
  simp only [diagonal_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_apply]
  simp only [diagonal_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

theorem trace_pow_walk (B : Matrix n n ℂ) (a : n → ℂ) (p q r : ℕ) :
    trace ((diagonal a) ^ p * B * (diagonal a) ^ q * B * (diagonal a) ^ r * B) =
      walk B (fun i j k ↦ a i ^ p * a j ^ q * a k ^ r) := by
  simpa only [mul_assoc, diagonal_pow, Pi.pow_apply] using
    trace_diagonal_walk B (a ^ p) (a ^ q) (a ^ r)

private theorem traceGap_diagonal (a : n → ℝ) (B : Matrix n n ℂ) :
    3 * traceGap (diagonal fun i ↦ (a i : ℂ)) B =
      walk B (fun i j k ↦ (cubicDefect (a i) (a j) (a k) : ℂ)) := by
  let d : n → ℂ := fun i ↦ (a i : ℂ)
  change 3 * traceGap (diagonal d) B = _
  rw [traceGap_eq_compositions]
  have hw (p q r : ℕ) := trace_pow_walk B d p q r
  rw [show trace (diagonal d ^ 3 * B ^ 3) = walk B (fun i j k ↦ d i ^ 3 * d j ^ 0 * d k ^ 0)
    by simpa only [pow_zero, one_mul, mul_one, pow_succ, mul_assoc] using hw 3 0 0]
  rw [show trace (B * diagonal d ^ 3 * B ^ 2) = walk B (fun i j k ↦ d i ^ 0 * d j ^ 3 * d k ^ 0)
    by simpa only [pow_zero, one_mul, mul_one, pow_succ, mul_assoc] using hw 0 3 0]
  rw [show trace (B ^ 2 * diagonal d ^ 3 * B) = walk B (fun i j k ↦ d i ^ 0 * d j ^ 0 * d k ^ 3)
    by simpa only [pow_zero, one_mul, mul_one, pow_succ, mul_assoc] using hw 0 0 3]
  rw [show trace (diagonal d ^ 2 * B * diagonal d * B ^ 2) = walk B (fun i j k ↦ d i ^ 2 * d j ^ 1 * d k ^ 0)
    by simpa only [pow_zero, one_mul, mul_one, pow_one, pow_succ, mul_assoc] using hw 2 1 0]
  rw [show trace (diagonal d ^ 2 * B ^ 2 * diagonal d * B) = walk B (fun i j k ↦ d i ^ 2 * d j ^ 0 * d k ^ 1)
    by simpa only [pow_zero, one_mul, mul_one, pow_one, pow_succ, mul_assoc] using hw 2 0 1]
  rw [show trace (diagonal d * B * diagonal d ^ 2 * B ^ 2) = walk B (fun i j k ↦ d i ^ 1 * d j ^ 2 * d k ^ 0)
    by simpa only [pow_zero, one_mul, mul_one, pow_one, pow_succ, mul_assoc] using hw 1 2 0]
  rw [show trace (B * diagonal d ^ 2 * B * diagonal d * B) = walk B (fun i j k ↦ d i ^ 0 * d j ^ 2 * d k ^ 1)
    by simpa only [pow_zero, one_mul, mul_one, pow_one, pow_succ, mul_assoc] using hw 0 2 1]
  rw [show trace (diagonal d * B ^ 2 * diagonal d ^ 2 * B) = walk B (fun i j k ↦ d i ^ 1 * d j ^ 0 * d k ^ 2)
    by simpa only [pow_zero, one_mul, mul_one, pow_one, pow_succ, mul_assoc] using hw 1 0 2]
  rw [show trace (B * diagonal d * B * diagonal d ^ 2 * B) = walk B (fun i j k ↦ d i ^ 0 * d j ^ 1 * d k ^ 2)
    by simpa only [pow_zero, one_mul, mul_one, pow_one, pow_succ, mul_assoc] using hw 0 1 2]
  rw [show trace ((diagonal d * B) ^ 3) = walk B (fun i j k ↦ d i ^ 1 * d j ^ 1 * d k ^ 1)
    by simpa only [pow_zero, one_mul, mul_one, pow_one, pow_succ, mul_assoc] using hw 1 1 1]
  have h9 (z : ℂ) : 9 * z = (9 : ℂ) • z := rfl
  simp only [h9, ← map_smul, ← map_add, ← map_sub]
  congr 1
  funext i j k
  simp [cubicDefect, d, smul_eq_mul]
  ring

private def centeredWeight (a : n → ℝ) (i j k : n) : ℂ :=
  ((a j - a i) * (a k - a i) * symmetricKernel (a i) (a j) (a k) : ℝ)

private theorem walk_cubicDefect (a : n → ℝ) (B : Matrix n n ℂ) :
    walk B (fun i j k ↦ (cubicDefect (a i) (a j) (a k) : ℂ)) =
      3 * walk B (centeredWeight a) := by
  have hw : (fun i j k ↦ (cubicDefect (a i) (a j) (a k) : ℂ)) =
      centeredWeight a + (fun i j k ↦ centeredWeight a j k i) +
        (fun i j k ↦ centeredWeight a k i j) := by
    funext i j k
    simp only [Pi.add_apply, centeredWeight]
    push_cast
    rw [cubicDefect_eq_cyclic_symmetric]
    push_cast
    ring
  have hrot := walk_rotate B (centeredWeight a)
  have hrot₂ := walk_rotate B (fun i j k ↦ centeredWeight a j k i)
  rw [hw, map_add, map_add, hrot₂, hrot]
  ring

private theorem centered_form (a : n → ℝ) (B : Matrix n n ℂ)
    (ha : ∀ i, 0 ≤ a i) (hB : B.PosSemidef) (i : n) :
    0 ≤ ∑ j, ∑ k, B i j * B j k * B k i * centeredWeight a i j k := by
  let G : Matrix n n ℝ := Matrix.of fun j k ↦ symmetricKernel (a i) (a j) (a k)
  have hG : G.PosSemidef := symmetricKernel_psd (a i) (ha i) a ha
  have hc := D5.S3.Weil.Probability.FiniteGaussianSchoenberg.ofReal_posSemidef G hG
  let v : n → ℂ := fun j ↦ ((a j - a i : ℝ) : ℂ) * B j i
  have hp : (B ⊙ G.map Complex.ofReal).PosSemidef := hB.hadamard hc
  convert hp.dotProduct_mulVec_nonneg v using 1
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  have hstar : star (B j i) = B i j := congrFun (congrFun hB.isHermitian i) j
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  simp only [centeredWeight, Pi.star_apply, v, star_mul, hreal,
    hstar, hadamard_apply, Matrix.map_apply, G, Matrix.of_apply, Complex.ofReal_mul]
  ring

private theorem traceGap_diagonal_nonneg_all (a : n → ℝ) (B : Matrix n n ℂ)
    (ha : ∀ i, 0 ≤ a i) (hB : B.PosSemidef) :
    0 ≤ (traceGap (diagonal fun i ↦ (a i : ℂ)) B).re := by
  have he := traceGap_diagonal a B
  rw [walk_cubicDefect] at he
  have h := congrArg Complex.re he
  norm_num [Complex.mul_re] at h
  have hn : 0 ≤ walk B (centeredWeight a) :=
    Finset.sum_nonneg fun i _ ↦ centered_form a B ha hB i
  have hn' := (Complex.nonneg_iff.mp hn).1
  linarith

/-- The exact cubic gap at a diagonal matrix with smallest eigenvalue zero. -/
theorem traceGap_diagonal_nonneg (a : Fin 4 → ℝ) (B : Matrix (Fin 4) (Fin 4) ℂ)
    (ha : ∀ i, 0 ≤ a i) (hz : ∃ i, a i = 0) (hB : B.PosSemidef) :
    0 ≤ (traceGap (diagonal fun i ↦ (a i : ℂ)) B).re := by
  clear hz
  exact traceGap_diagonal_nonneg_all a B ha hB

/-- The mean trace of the twenty words with three copies of each PSD factor
is at least the alternating trace in every finite dimension. -/
theorem E33_all (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace ((A * B) ^ 3) ≤ wordMean A B := by
  let U := hA.isHermitian.eigenvectorUnitary
  let a := hA.isHermitian.eigenvalues
  let B' := Unitary.conjStarAlgAut ℂ _ (star U) B
  have hB' : B'.PosSemidef := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) B).PosSemidef
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hB.conjTranspose_mul_mul_same (U : Matrix n n ℂ)
  have hg := traceGap_diagonal_nonneg_all a B' hA.eigenvalues_nonneg hB'
  change 0 ≤ (traceGap (diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues)) B').re at hg
  rw [← hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary] at hg
  change 0 ≤ (traceGap (Unitary.conjStarAlgAut ℂ _ (star U) A)
    (Unitary.conjStarAlgAut ℂ _ (star U) B)).re at hg
  rw [traceGap_conj, traceGap_eq_mean] at hg
  norm_num [Complex.mul_re, Complex.div_re, Complex.sub_re] at hg
  refine Complex.le_def.mpr ⟨by linarith, ?_⟩
  rw [(Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
    (trace_cube_isSelfAdjoint A B hA.isHermitian hB.isHermitian),
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
      (wordMean_isSelfAdjoint A B hA.isHermitian hB.isHermitian)]

/-- The refined BMV product bound for three copies of each factor in dimension four. -/
theorem E33 (A B : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (trace ((A * B) ^ 3)).re ≤ (wordMean A B).re :=
  (Complex.le_def.mp (E33_all A B hA hB)).1

theorem E33_complex (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace ((A * B) ^ 3) ≤ wordMean A B :=
  E33_all A B hA hB

#print axioms E33_all
#print axioms traceGap_diagonal_nonneg
#print axioms E33

end RefinedBMV
