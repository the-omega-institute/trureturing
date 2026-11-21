/- GID: D5/S3/Quantum/Analysis/RefinedBMV33
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV33
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The four-dimensional refined BMV product bound follows from positive closed-walk Schur forms. -/

import D5.S3.Quantum.Analysis.RefinedBMVKernel
import D5.S3.Quantum.Analysis.RefinedBMVWords
import D5.S3.Weil.Probability.FiniteGaussianSchoenberg

open Matrix
open scoped ComplexOrder BigOperators

noncomputable section

namespace RefinedBMV

variable {n : Type*} [Fintype n] [DecidableEq n]

private def walk (B : Matrix n n ℂ) : (n → n → n → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ i, ∑ j, ∑ k, B i j * B j k * B k i * f i j k
  map_add' f g := by simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

private theorem walk_rotate (B : Matrix n n ℂ) (f : n → n → n → ℂ) :
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

private theorem trace_pow_walk (B : Matrix n n ℂ) (a : n → ℂ) (p q r : ℕ) :
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
  ((a j - a i) * (a k - a i) * kernel (a i) (a j) (a k) : ℝ)

private theorem walk_cubicDefect (a : n → ℝ) (B : Matrix n n ℂ) :
    walk B (fun i j k ↦ (cubicDefect (a i) (a j) (a k) : ℂ)) =
      3 * walk B (centeredWeight a) := by
  have hw : (fun i j k ↦ (cubicDefect (a i) (a j) (a k) : ℂ)) =
      centeredWeight a + (fun i j k ↦ centeredWeight a j k i) +
        (fun i j k ↦ centeredWeight a k i j) := by
    funext i j k
    simp only [Pi.add_apply, centeredWeight]
    push_cast
    rw [cubicDefect_eq_cyclic]
    push_cast
    ring
  have hrot := walk_rotate B (centeredWeight a)
  have hrot₂ := walk_rotate B (fun i j k ↦ centeredWeight a j k i)
  rw [hw, map_add, map_add, hrot₂, hrot]
  ring

private theorem centered_form (a : Fin 4 → ℝ) (B : Matrix (Fin 4) (Fin 4) ℂ)
    (ha : ∀ i, 0 ≤ a i) (hz : ∃ i, a i = 0) (hB : B.PosSemidef) (i : Fin 4) :
    0 ≤ ∑ j, ∑ k, B i j * B j k * B k i * centeredWeight a i j k := by
  let x : Fin 3 → ℝ := fun j ↦ a (i.succAbove j)
  let G : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun j k ↦ kernel (a i) (x j) (x k)
  have hG : G.PosSemidef := by
    rcases (ha i).eq_or_lt with he | hp
    · simpa [G, ← he] using kernel_zero_psd x (fun j ↦ ha _)
    · obtain ⟨k, hk⟩ := hz
      have hki : k ≠ i := by rintro rfl; exact hp.ne' hk
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hki
      exact kernel_pos_psd (a i) hp x (fun j ↦ ha _) ⟨j, by simpa [x, hj] using hk⟩
  have hc := D5.S3.Weil.Probability.FiniteGaussianSchoenberg.ofReal_posSemidef G hG
  let v : Fin 3 → ℂ := fun j ↦ ((x j - a i : ℝ) : ℂ) * B (i.succAbove j) i
  have hp : (B.submatrix i.succAbove i.succAbove ⊙ G.map Complex.ofReal).PosSemidef :=
    (hB.submatrix i.succAbove).hadamard hc
  let term (j k : Fin 4) := B i j * B j k * B k i * centeredWeight a i j k
  have hj (k : Fin 4) : term i k = 0 := by simp [term, centeredWeight]
  have hk (j : Fin 4) : term j i = 0 := by simp [term, centeredWeight]
  change 0 ≤ ∑ j, ∑ k, term j k
  rw [Fin.sum_univ_succAbove (fun j ↦ ∑ k, term j k) i]
  simp only [hj, Finset.sum_const_zero, zero_add]
  simp_rw [Fin.sum_univ_succAbove (term (i.succAbove _)) i, hk, zero_add]
  convert hp.dotProduct_mulVec_nonneg v using 1
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  have hstar : star (B (i.succAbove j) i) = B i (i.succAbove j) :=
    congrFun (congrFun hB.isHermitian i) (i.succAbove j)
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  simp only [term, centeredWeight, Pi.star_apply, v, star_mul, hreal,
    hstar, hadamard_apply, submatrix_apply,
    Matrix.map_apply, G, Matrix.of_apply, Complex.ofReal_mul, x]
  ring

/-- The exact cubic gap at a diagonal matrix with smallest eigenvalue zero. -/
theorem traceGap_diagonal_nonneg (a : Fin 4 → ℝ) (B : Matrix (Fin 4) (Fin 4) ℂ)
    (ha : ∀ i, 0 ≤ a i) (hz : ∃ i, a i = 0) (hB : B.PosSemidef) :
    0 ≤ (traceGap (diagonal fun i ↦ (a i : ℂ)) B).re := by
  have he := traceGap_diagonal a B
  rw [walk_cubicDefect] at he
  have h := congrArg Complex.re he
  norm_num [Complex.mul_re] at h
  have hn : 0 ≤ walk B (centeredWeight a) := by
    exact Finset.sum_nonneg fun i _ ↦ centered_form a B ha hz hB i
  have hn' := (Complex.nonneg_iff.mp hn).1
  linarith

/-- The refined BMV product bound for three copies of each factor in dimension four. -/
theorem E33 (A B : Matrix (Fin 4) (Fin 4) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (trace ((A * B) ^ 3)).re ≤ (wordMean A B).re := by
  let U := hA.isHermitian.eigenvectorUnitary
  let a := hA.isHermitian.eigenvalues
  let B' := Unitary.conjStarAlgAut ℂ _ (star U) B
  have hB' : B'.PosSemidef := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) B).PosSemidef
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hB.conjTranspose_mul_mul_same (U : Matrix (Fin 4) (Fin 4) ℂ)
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  let t := a i
  have ht : 0 ≤ t := hA.eigenvalues_nonneg i
  let b := fun j ↦ a j - t
  have hb (j : Fin 4) : 0 ≤ b j := sub_nonneg.mpr (hi j (Finset.mem_univ j))
  have hb₀ : ∃ j, b j = 0 := ⟨i, sub_self _⟩
  let D := diagonal fun j ↦ (b j : ℂ)
  have hD : D.IsHermitian := (posSemidef_diagonal_iff.mpr
    (fun j ↦ Complex.zero_le_real.mpr (hb j))).isHermitian
  have hdiag : Unitary.conjStarAlgAut ℂ _ (star U) A = D + (t : ℂ) • 1 := by
    rw [hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
    ext j k
    by_cases hjk : j = k
    · subst k
      simp [D, b, a, Matrix.one_apply, smul_eq_mul]
    · simp [D, Matrix.diagonal_apply_ne _ hjk, Matrix.one_apply, hjk]
  have hg := (traceGap_diagonal_nonneg b B' hb hb₀ hB').trans (traceGap_shift D B' hD hB' t ht)
  rw [← hdiag] at hg
  change 0 ≤ (traceGap (Unitary.conjStarAlgAut ℂ _ (star U) A)
    (Unitary.conjStarAlgAut ℂ _ (star U) B)).re at hg
  rw [traceGap_conj, traceGap_eq_mean] at hg
  norm_num [Complex.mul_re, Complex.div_re, Complex.sub_re] at hg
  linarith

theorem E33_complex (A B : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace ((A * B) ^ 3) ≤ wordMean A B := by
  refine Complex.le_def.mpr ⟨E33 A B hA hB, ?_⟩
  rw [(Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
    (trace_cube_isSelfAdjoint A B hA.isHermitian hB.isHermitian),
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
      (wordMean_isSelfAdjoint A B hA.isHermitian hB.isHermitian)]

#print axioms traceGap_diagonal_nonneg
#print axioms E33

end RefinedBMV
