/- GID: D5/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/PetzErasureGramBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Gram bound for the ordinary Petz benchmark under complete erasure. -/

/-
proof_shape: content
admission_basis: escape-witness
escape_witness: The diagonal and off-diagonal entries of the squared roots
give the two residual identities in `residual_norm_sq`. Their joint
constraint yields a nonnegative defect and bounds the orthogonal population
numerator of the benchmark.
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Gram estimate for the ordinary Petz benchmark under complete erasure

The Hilbert-space estimate uses the two diagonal identities of the squared
root together with the pairing from its lower off-diagonal entry.
-/

open scoped BigOperators InnerProductSpace ComplexConjugate Matrix Matrix.Norms.Frobenius

noncomputable section

namespace D5.S3.Quantum.Recovery.LocalCompression.PetzErasureGramBound

set_option autoImplicit false

section HilbertSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem norm_ofReal_smul (r : ℝ) (X : E) :
    ‖(r : ℂ) • X‖ = |r| * ‖X‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- The residuals about the normalized sum of the two diagonal root blocks. -/
theorem residual_norm_sq {A C B h : E} {a c δ : ℝ} {b : ℂ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hs : 0 < a + c)
    (hA : ‖A‖ ^ 2 = a ^ 2 - δ) (hC : ‖C‖ ^ 2 = c ^ 2 - δ)
    (hB : ‖B‖ ^ 2 = ‖b‖ ^ 2 + δ)
    (hsum : ((a + c : ℝ) : ℂ) • h = A + C)
    (hinner : ⟪h, B⟫_ℂ = b) :
    ‖B - b • h‖ ^ 2 = δ - (1 - ‖h‖ ^ 2) * ‖b‖ ^ 2 ∧
    ‖A - (a : ℂ) • h‖ ^ 2 = a * c * (1 - ‖h‖ ^ 2) - δ := by
  constructor
  · have hpair : ⟪B, b • h⟫_ℂ = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_smul_right, ← inner_conj_symm B h, hinner, Complex.mul_conj']
      exact (Complex.ofReal_pow ‖b‖ 2).symm
    rw [norm_sub_sq (𝕜 := ℂ), hpair, RCLike.re_eq_complex_re, Complex.ofReal_re, hB, norm_smul]
    ring
  · have hscaled :
        ((a + c : ℝ) : ℂ) • (A - (a : ℂ) • h) = (c : ℂ) • A - (a : ℂ) • C := by
      rw [smul_sub, smul_smul, mul_comm (↑(a + c) : ℂ) (a : ℂ), ← smul_smul, hsum,
        Complex.ofReal_add, add_smul, smul_add]
      abel
    have hnorm (X : E) : ‖((a + c : ℝ) : ℂ) • X‖ ^ 2 =
        (a + c) ^ 2 * ‖X‖ ^ 2 := by
      rw [norm_ofReal_smul, abs_of_pos hs, mul_pow]
    have hweighted :
        ‖(c : ℂ) • A - (a : ℂ) • C‖ ^ 2 + a * c * ‖A + C‖ ^ 2 =
          (a + c) * (c * ‖A‖ ^ 2 + a * ‖C‖ ^ 2) := by
      rw [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ)]
      simp only [norm_ofReal_smul, abs_of_nonneg ha, abs_of_nonneg hc,
        inner_smul_left, inner_smul_right, Complex.conj_ofReal, RCLike.re_eq_complex_re,
        mul_assoc, Complex.re_ofReal_mul]
      ring
    rw [← hscaled, hnorm, ← hsum, hnorm, hA, hC] at hweighted
    apply mul_left_cancel₀ (pow_ne_zero 2 hs.ne')
    linear_combination hweighted

/-- The scalar marginal root determinant condition implies a nonnegative defect. -/
theorem defect_nonneg {A C B h : E} {a c δ : ℝ} {b : ℂ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hs : 0 < a + c)
    (hA : ‖A‖ ^ 2 = a ^ 2 - δ) (hC : ‖C‖ ^ 2 = c ^ 2 - δ)
    (hB : ‖B‖ ^ 2 = ‖b‖ ^ 2 + δ)
    (hsum : ((a + c : ℝ) : ℂ) • h = A + C)
    (hinner : ⟪h, B⟫_ℂ = b) (hdet : ‖b‖ ^ 2 ≤ a * c) :
    0 ≤ δ := by
  have hres := (residual_norm_sq ha hc hs hA hC hB hsum hinner).2
  have hbudget : a * c * ‖h‖ ^ 2 ≤ a * c - δ := by
    nlinarith only [hres, sq_nonneg ‖A - (a : ℂ) • h‖]
  have hCS : ‖b‖ ^ 2 ≤ ‖h‖ ^ 2 * ‖B‖ ^ 2 := by
    rw [← mul_pow]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
    rw [← hinner]
    exact norm_inner_le_norm (𝕜 := ℂ) h B
  have hproduct : a * c * ‖b‖ ^ 2 ≤ (a * c - δ) * (‖b‖ ^ 2 + δ) := calc
    _ ≤ a * c * (‖h‖ ^ 2 * ‖B‖ ^ 2) := mul_le_mul_of_nonneg_left hCS (mul_nonneg ha hc)
    _ = (a * c * ‖h‖ ^ 2) * ‖B‖ ^ 2 := by ring
    _ ≤ (a * c - δ) * ‖B‖ ^ 2 := mul_le_mul_of_nonneg_right hbudget (sq_nonneg _)
    _ = _ := by rw [hB]
  by_contra! hneg
  have hsign := mul_nonneg (sub_nonneg.mpr hdet) (neg_nonneg.mpr hneg.le)
  nlinarith only [hproduct, hsign, mul_pos_of_neg_of_neg hneg hneg]

private theorem cauchy_two (u v x y : ℝ) :
    (u * x + v * y) ^ 2 ≤ (u ^ 2 + v ^ 2) * (x ^ 2 + y ^ 2) := by
  nlinarith only [sq_nonneg (u * y - v * x)]

/-- The residual estimate for complex Hilbert-space vectors. The real part
of the mutual pairing of the diagonal blocks suffices in the expansion. -/
theorem gram_bound {A C B h : E} {a c δ : ℝ} {b : ℂ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hs : 0 < a + c) (hδ : 0 ≤ δ)
    (hA : ‖A‖ ^ 2 = a ^ 2 - δ) (hC : ‖C‖ ^ 2 = c ^ 2 - δ)
    (hB : ‖B‖ ^ 2 = ‖b‖ ^ 2 + δ)
    (hsum : ((a + c : ℝ) : ℂ) • h = A + C)
    (hinner : ⟪h, B⟫_ℂ = b) :
    ‖(a : ℂ) • B - b • A‖ ^ 2 ≤ (a ^ 2 + a * c) * δ := by
  obtain ⟨hBres, hAres⟩ := residual_norm_sq ha hc hs hA hC hB hsum hinner
  have hnA : ‖A‖ ≤ a :=
    (sq_le_sq₀ (norm_nonneg _) ha).1 (by linarith only [hA, hδ])
  have hnC : ‖C‖ ≤ c :=
    (sq_le_sq₀ (norm_nonneg _) hc).1 (by linarith only [hC, hδ])
  have hn : ‖h‖ ≤ 1 := by
    have hmul : (a + c) * ‖h‖ ≤ (a + c) * 1 := calc
      _ = ‖A + C‖ := by rw [← hsum, norm_ofReal_smul, abs_of_pos hs]
      _ ≤ ‖A‖ + ‖C‖ := norm_add_le _ _
      _ ≤ (a + c) * 1 := by rw [mul_one]; exact add_le_add hnA hnC
    exact le_of_mul_le_mul_left hmul hs
  let t := (1 - ‖h‖ ^ 2) * ‖b‖ ^ 2
  let x := ‖B - b • h‖
  let y := ‖b‖ * ‖A - (a : ℂ) • h‖
  have ht : 0 ≤ t := by
    have hsq := (sq_le_sq₀ (norm_nonneg h) (zero_le_one : (0 : ℝ) ≤ 1)).2 hn
    exact mul_nonneg (sub_nonneg.mpr (by simpa only [one_pow] using hsq)) (sq_nonneg _)
  have hxt : x ^ 2 + t = δ := by
    change x ^ 2 = δ - t at hBres
    linarith only [hBres]
  have hy : y ^ 2 ≤ a * c * t := calc
    _ = ‖b‖ ^ 2 * ‖A - (a : ℂ) • h‖ ^ 2 := by dsimp only [y]; rw [mul_pow]
    _ ≤ ‖b‖ ^ 2 * (a * c * (1 - ‖h‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hAres, hδ]) (sq_nonneg _)
    _ = _ := by dsimp only [t]; ring
  have hsqrtac := Real.sq_sqrt (mul_nonneg ha hc)
  have hsqrtt := Real.sq_sqrt ht
  have hyr : y ≤ Real.sqrt (a * c) * Real.sqrt t := by
    apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1
    rwa [mul_pow (Real.sqrt (a * c)) (Real.sqrt t) 2, hsqrtac, hsqrtt]
  have hsplit :
      (a : ℂ) • B - b • A =
        (a : ℂ) • (B - b • h) - b • (A - (a : ℂ) • h) := by
    rw [smul_sub, smul_sub, smul_smul, smul_smul, mul_comm b (a : ℂ)]
    abel
  have htriangle :
      ‖(a : ℂ) • B - b • A‖ ≤ a * x + Real.sqrt (a * c) * Real.sqrt t := calc
    _ ≤ a * x + y := by
      rw [hsplit]
      simpa only [x, y, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] using
        (norm_sub_le ((a : ℂ) • (B - b • h)) (b • (A - (a : ℂ) • h)))
    _ ≤ _ := add_le_add_right hyr (a * x)
  calc
    _ ≤ (a * x + Real.sqrt (a * c) * Real.sqrt t) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans htriangle)).2 htriangle
    _ ≤ (a ^ 2 + (Real.sqrt (a * c)) ^ 2) * (x ^ 2 + (Real.sqrt t) ^ 2) :=
      cauchy_two a (Real.sqrt (a * c)) x (Real.sqrt t)
    _ = _ := by rw [hsqrtac, hsqrtt, hxt]

end HilbertSpace

private theorem quadratic_gap (a c : ℝ) :
    (1 + Real.sqrt 2) / 2 * (a ^ 2 + c ^ 2) - (a ^ 2 + a * c) =
      (1 + Real.sqrt 2) / 2 * (c - (Real.sqrt 2 - 1) * a) ^ 2 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination (((1 - Real.sqrt 2) / 2) * a ^ 2 + a * c) * hs

/-- The sharp quadratic coefficient relative to `a ^ 2 + c ^ 2`. -/
theorem quadratic_bound (a c : ℝ) :
    a ^ 2 + a * c ≤ (1 + Real.sqrt 2) / 2 * (a ^ 2 + c ^ 2) := by
  apply sub_nonneg.mp
  rw [quadratic_gap]
  exact mul_nonneg (by positivity) (sq_nonneg _)

/-- Equality at `(1, √2 - 1)` gives sharpness on the nonnegative quadrant. -/
theorem quadratic_coefficient_isLeast :
    IsLeast {k : ℝ | ∀ a c : ℝ, 0 ≤ a → 0 ≤ c → a ^ 2 + a * c ≤ k * (a ^ 2 + c ^ 2)}
      ((1 + Real.sqrt 2) / 2) := by
  refine ⟨fun a c _ _ => quadratic_bound a c, ?_⟩
  intro k hk
  change ∀ a c : ℝ, 0 ≤ a → 0 ≤ c → a ^ 2 + a * c ≤ k * (a ^ 2 + c ^ 2) at hk
  have hc : 0 ≤ Real.sqrt 2 - 1 := sub_nonneg.mpr (Real.le_sqrt_of_sq_le (by norm_num))
  have heq := quadratic_gap 1 (Real.sqrt 2 - 1)
  rw [mul_one, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at heq
  have hpos : 0 < (1 : ℝ) ^ 2 + (Real.sqrt 2 - 1) ^ 2 := by positivity
  apply le_of_mul_le_mul_right _ hpos
  rw [sub_eq_zero.mp heq]
  exact hk 1 (Real.sqrt 2 - 1) zero_le_one hc

section Matrix

open Matrix

variable {ι : Type*} [Fintype ι]

private def hsCoords (X : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 X.vec

private theorem hsCoords_norm (X : Matrix ι ι ℂ) : ‖hsCoords X‖ = ‖X‖ := by
  rw [hsCoords, PiLp.norm_eq_of_L2, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Fintype.sum_prod_type, Matrix.vec, Real.rpow_two]
  rw [Finset.sum_comm]

private theorem hsCoords_inner (X Y : Matrix ι ι ℂ) :
    ⟪hsCoords X, hsCoords Y⟫_ℂ = (Xᴴ * Y).trace := by
  unfold hsCoords
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  exact Matrix.star_vec_dotProduct_vec X Y

private theorem trace_adjoint_mul_self (X : Matrix ι ι ℂ) :
    (Xᴴ * X).trace = ((‖X‖ ^ 2 : ℝ) : ℂ) := by
  rw [← hsCoords_inner, inner_self_eq_norm_sq_to_K, hsCoords_norm]
  exact (Complex.ofReal_pow ‖X‖ 2).symm

/-- The Hilbert–Schmidt pairing of Hermitian blocks is real. -/
theorem hermitian_trace_mul_im (A C : Matrix ι ι ℂ) (hA : Aᴴ = A) (hC : Cᴴ = C) :
    (A * C).trace.im = 0 := by
  have hstar : conj ((A * C).trace) = (A * C).trace := by
    calc
      _ = ((A * C)ᴴ).trace := by
        simpa only [Complex.star_def] using (Matrix.trace_conjTranspose (A * C)).symm
      _ = _ := by rw [Matrix.conjTranspose_mul, hA, hC, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.mp hstar

/-- Partial trace over the environment in the block presentation of a qubit. -/
def traceBlocks (S : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![S.toBlocks₁₁.trace, S.toBlocks₁₂.trace; S.toBlocks₂₁.trace, S.toBlocks₂₂.trace]

/-- The block traces of the squared joint root supply the two diagonal
norm identities and the lower off-diagonal pairing. -/
theorem traceBlocks_root_mul (A C B : Matrix ι ι ℂ) (hA : Aᴴ = A) (hC : Cᴴ = C) :
    traceBlocks (fromBlocks A Bᴴ B C * fromBlocks A Bᴴ B C) =
      !![↑(‖A‖ ^ 2 + ‖B‖ ^ 2 : ℝ), (A * Bᴴ + Bᴴ * C).trace;
         ((A + C) * B).trace, ↑(‖C‖ ^ 2 + ‖B‖ ^ 2 : ℝ)] := by
  have hAA := trace_adjoint_mul_self A
  have hCC := trace_adjoint_mul_self C
  rw [hA] at hAA
  rw [hC] at hCC
  have hBB := trace_adjoint_mul_self B
  have hBB' : (B * Bᴴ).trace = ((‖B‖ ^ 2 : ℝ) : ℂ) :=
    (Matrix.trace_mul_comm B Bᴴ).trans hBB
  have hBA : (B * A + C * B).trace = ((A + C) * B).trace := by
    rw [add_mul, Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm B A]
  simp only [Matrix.fromBlocks_multiply, traceBlocks, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂]
  rw [hBA]
  simp only [Matrix.trace_add, hAA, hCC, hBB, hBB', Complex.ofReal_add]
  rw [add_comm (((‖B‖ ^ 2 : ℝ) : ℂ)) (((‖C‖ ^ 2 : ℝ) : ℂ))]

/-- Hilbert–Schmidt estimate when the squared marginal root equals the
partial trace of the squared joint root. The determinant condition is
`‖b‖ ^ 2 ≤ a * c`, so singular roots are included. -/
theorem matrix_gram_bound (A C B : Matrix ι ι ℂ) (a c : ℝ) (b : ℂ)
    (hA : Aᴴ = A) (hC : Cᴴ = C)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hs : 0 < a + c) (hdet : ‖b‖ ^ 2 ≤ a * c)
    (hmarginal : traceBlocks (fromBlocks A Bᴴ B C * fromBlocks A Bᴴ B C) =
      !![(a : ℂ), conj b; b, (c : ℂ)] * !![(a : ℂ), conj b; b, (c : ℂ)]) :
    0 ≤ ‖B‖ ^ 2 - ‖b‖ ^ 2 ∧
      ‖(a : ℂ) • B - b • A‖ ^ 2 ≤ (a ^ 2 + a * c) * (‖B‖ ^ 2 - ‖b‖ ^ 2) := by
  rw [traceBlocks_root_mul A C B hA hC] at hmarginal
  have hdiagA : ‖A‖ ^ 2 + ‖B‖ ^ 2 = a ^ 2 + ‖b‖ ^ 2 := by
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) hmarginal
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.conj_mul', ← Complex.ofReal_mul, ← Complex.ofReal_add,
      Complex.ofReal_re, pow_two] using hentry
  have hdiagC : ‖C‖ ^ 2 + ‖B‖ ^ 2 = c ^ 2 + ‖b‖ ^ 2 := by
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).re) hmarginal
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.mul_conj', ← Complex.ofReal_mul, Complex.add_re,
      Complex.ofReal_re, pow_two, add_comm] using hentry
  have hcross : ((A + C) * B).trace = ((a + c : ℝ) : ℂ) * b := by
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hmarginal
    calc
      _ = b * (a : ℂ) + (c : ℂ) * b := by
        simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one] using hentry
      _ = _ := by push_cast; ring
  let δ := ‖B‖ ^ 2 - ‖b‖ ^ 2
  let h := (((a + c)⁻¹ : ℝ) : ℂ) • (hsCoords A + hsCoords C)
  have hsum : ((a + c : ℝ) : ℂ) • h = hsCoords A + hsCoords C := by
    dsimp only [h]
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne', Complex.ofReal_one, one_smul]
  have hadd : hsCoords (A + C) = hsCoords A + hsCoords C := rfl
  have hpair : ⟪h, hsCoords B⟫_ℂ = b := by
    apply mul_left_cancel₀
      (show ((a + c : ℝ) : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hs.ne')
    calc
      _ = ⟪((a + c : ℝ) : ℂ) • h, hsCoords B⟫_ℂ := by
        simpa only [Complex.conj_ofReal] using
          (inner_smul_left h (hsCoords B) ((a + c : ℝ) : ℂ)).symm
      _ = ((A + C) * B).trace := by
        rw [hsum, ← hadd, hsCoords_inner, Matrix.conjTranspose_add, hA, hC]
      _ = _ := hcross
  have hnormA : ‖hsCoords A‖ ^ 2 = a ^ 2 - δ := by
    rw [hsCoords_norm]
    dsimp only [δ]
    linarith only [hdiagA]
  have hnormC : ‖hsCoords C‖ ^ 2 = c ^ 2 - δ := by
    rw [hsCoords_norm]
    dsimp only [δ]
    linarith only [hdiagC]
  have hnormB : ‖hsCoords B‖ ^ 2 = ‖b‖ ^ 2 + δ := by
    rw [hsCoords_norm]
    dsimp only [δ]
    ring
  have hδ := defect_nonneg ha hc hs hnormA hnormC hnormB hsum hpair hdet
  have hgram := gram_bound ha hc hs hδ hnormA hnormC hnormB hsum hpair
  have hlinear : hsCoords ((a : ℂ) • B - b • A) =
      (a : ℂ) • hsCoords B - b • hsCoords A := rfl
  rw [← hlinear, hsCoords_norm] at hgram
  exact ⟨hδ, hgram⟩

/-- The unnormalized orthogonal population of the rank-one benchmark.
The four traces are the entries of the benchmark Gram matrix, tested against
the column with entries `-conj b` and `a`. -/
theorem benchmark_orthogonal_numerator (A B : Matrix ι ι ℂ) (a : ℝ) (b : ℂ) :
    ((‖(a : ℂ) • B - b • A‖ ^ 2 : ℝ) : ℂ) =
      b * conj b * (A * Aᴴ).trace - (a : ℂ) * b * (A * Bᴴ).trace -
        (a : ℂ) * conj b * (B * Aᴴ).trace + (a : ℂ) ^ 2 * (B * Bᴴ).trace := by
  rw [← trace_adjoint_mul_self,
    Matrix.trace_mul_comm (((a : ℂ) • B - b • A)ᴴ) ((a : ℂ) • B - b • A)]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul]
  ring

end Matrix

end D5.S3.Quantum.Recovery.LocalCompression.PetzErasureGramBound
