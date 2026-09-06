/- GID: D5/S3/Quantum/Tomography/OrderThreeComplementaryContextRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/OrderThreeComplementaryContextRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A trace-zero order-three unitary in the sum of two mutually unbiased diagonal algebras lies entirely in one of them. -/

import D5.S3.Quantum.Tomography.RankOneContextCommutator

/- Reuse audit (2026-09-05):
   Reuses RankOneContext, overlap, the rank-one projection laws, Matrix.trace,
   complex conjugation, and finite spectral sums. No second basis, unitary,
   pinching, Hadamard, affinity, or flatness carrier is introduced. The private
   abbreviation below only shortens the existing finite spectral sum.
   The result is independent of the unproved strict-X affinity bound and of
   any proposed enumeration of common-unbiased vectors. In particular it does
   not assume the disproved rowwise collision threshold.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.OrderThreeComplementaryContextRigidity

open Matrix
open D5.S3.Quantum.Tomography.RankOneContextCommutator

private abbrev diagonalElement {d : ℕ} (C : RankOneContext d)
    (a : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, a i • C.projector i

private theorem projector_mul_diagonal {d : ℕ}
    (C : RankOneContext d)
    (hC : ∀ i j, i ≠ j → C.projector i * C.projector j = 0)
    (a : Fin d → ℂ) (i : Fin d) :
    C.projector i * diagonalElement C a = a i • C.projector i := by
  classical
  unfold diagonalElement
  rw [Matrix.mul_sum]
  simp_rw [Matrix.mul_smul]
  rw [Finset.sum_eq_single i]
  · rw [(C.rankOne i).2.1]
  · intro j _ hji
    rw [hC i j hji.symm, smul_zero]
  · simp

private theorem diagonal_mul_projector {d : ℕ}
    (C : RankOneContext d)
    (hC : ∀ i j, i ≠ j → C.projector i * C.projector j = 0)
    (a : Fin d → ℂ) (i : Fin d) :
    diagonalElement C a * C.projector i = a i • C.projector i := by
  classical
  unfold diagonalElement
  rw [Matrix.sum_mul]
  simp_rw [Matrix.smul_mul]
  rw [Finset.sum_eq_single i]
  · rw [(C.rankOne i).2.1]
  · intro j _ hji
    rw [hC j i hji, smul_zero]
  · simp

private theorem diagonal_mul_diagonal {d : ℕ}
    (C : RankOneContext d)
    (hC : ∀ i j, i ≠ j → C.projector i * C.projector j = 0)
    (a c : Fin d → ℂ) :
    diagonalElement C a * diagonalElement C c =
      diagonalElement C (fun i ↦ a i * c i) := by
  change (∑ i, a i • C.projector i) * diagonalElement C c = _
  rw [Matrix.sum_mul]
  simp_rw [Matrix.smul_mul, projector_mul_diagonal C hC c, smul_smul]
  rfl

private theorem diagonal_adjoint {d : ℕ}
    (C : RankOneContext d) (a : Fin d → ℂ) :
    (diagonalElement C a)ᴴ = diagonalElement C (fun i ↦ star (a i)) := by
  classical
  have hStar : ∀ i, (C.projector i)ᴴ = C.projector i :=
    fun i ↦ (C.rankOne i).1
  simp [diagonalElement, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul, hStar]

private theorem trace_projector_diagonal {d : ℕ}
    (C : RankOneContext d)
    (hC : ∀ i j, i ≠ j → C.projector i * C.projector j = 0)
    (a : Fin d → ℂ) (i : Fin d) :
    trace (C.projector i * diagonalElement C a) = a i := by
  rw [projector_mul_diagonal C hC, Matrix.trace_smul,
    (C.rankOne i).2.2.1]
  simp

private theorem trace_projector_other_diagonal {d : ℕ}
    (C D : RankOneContext d)
    (hCD : ∀ i j, trace (C.projector i * D.projector j) = (d : ℂ)⁻¹)
    (b : Fin d → ℂ) (i : Fin d) :
    trace (C.projector i * diagonalElement D b) =
      (d : ℂ)⁻¹ * ∑ j, b j := by
  simp only [diagonalElement, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, hCD, smul_eq_mul]
  rw [← Finset.sum_mul]
  ring

/- A single spectral-product computation is used twice: first for SSᴴ,
   and then for S². The cross terms vanish because both other-context
   coefficient lists have zero sum. -/
private theorem trace_projector_product_of_sums {d : ℕ}
    (C D : RankOneContext d)
    (hC : ∀ i j, i ≠ j → C.projector i * C.projector j = 0)
    (hD : ∀ i j, i ≠ j → D.projector i * D.projector j = 0)
    (hCD : ∀ i j, trace (C.projector i * D.projector j) = (d : ℂ)⁻¹)
    (a b c e : Fin d → ℂ)
    (hb : ∑ j, b j = 0) (he : ∑ j, e j = 0)
    (i : Fin d) :
    trace (C.projector i *
        ((diagonalElement C a + diagonalElement D b) *
          (diagonalElement C c + diagonalElement D e))) =
      a i * c i + (d : ℂ)⁻¹ * ∑ j, b j * e j := by
  let A := diagonalElement C a
  let B := diagonalElement D b
  let V := diagonalElement C c
  let W := diagonalElement D e
  have hPA : C.projector i * A = a i • C.projector i :=
    projector_mul_diagonal C hC a i
  have hPV : trace (C.projector i * V) = c i :=
    trace_projector_diagonal C hC c i
  have hVP : V * C.projector i = c i • C.projector i :=
    diagonal_mul_projector C hC c i
  have hPB : trace (C.projector i * B) = 0 := by
    change trace (C.projector i * diagonalElement D b) = 0
    rw [trace_projector_other_diagonal C D hCD, hb, mul_zero]
  have hPW : trace (C.projector i * W) = 0 := by
    change trace (C.projector i * diagonalElement D e) = 0
    rw [trace_projector_other_diagonal C D hCD, he, mul_zero]
  have hAV : trace (C.projector i * (A * V)) = a i * c i := by
    rw [← Matrix.mul_assoc, hPA, Matrix.smul_mul, Matrix.trace_smul, hPV]
    rfl
  have hAW : trace (C.projector i * (A * W)) = 0 := by
    rw [← Matrix.mul_assoc, hPA, Matrix.smul_mul, Matrix.trace_smul, hPW]
    simp
  have hBV : trace (C.projector i * (B * V)) = 0 := by
    calc
      trace (C.projector i * (B * V)) = trace (V * (C.projector i * B)) := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = trace ((V * C.projector i) * B) := by rw [Matrix.mul_assoc]
      _ = 0 := by
        rw [hVP, Matrix.smul_mul, Matrix.trace_smul, hPB]
        simp
  have hBW : trace (C.projector i * (B * W)) =
      (d : ℂ)⁻¹ * ∑ j, b j * e j := by
    change trace (C.projector i * (diagonalElement D b * diagonalElement D e)) = _
    rw [diagonal_mul_diagonal D hD,
      trace_projector_other_diagonal C D hCD]
  change trace (C.projector i * ((A + B) * (V + W))) = _
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    hAV, hAW, hBV, hBW]
  ring

private theorem complex_overlap_of_real_overlap {d : ℕ}
    (C D : RankOneContext d)
    (hMUB : ∀ i j, overlap C D i j = (d : ℝ)⁻¹) :
    ∀ i j, trace (C.projector i * D.projector j) = (d : ℂ)⁻¹ := by
  intro i j
  have hStar : star (trace (C.projector i * D.projector j)) =
      trace (C.projector i * D.projector j) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      (C.rankOne i).1, (D.rankOne j).1, Matrix.trace_mul_comm]
  have hIm := congrArg Complex.im hStar
  simp only [Complex.star_def, Complex.conj_im] at hIm
  have hZero : (trace (C.projector i * D.projector j)).im = 0 := by linarith
  have hCast : (d : ℂ)⁻¹ = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [hCast]
  apply Complex.ext
  · exact hMUB i j
  · simpa using hZero

private theorem normSq_star_sub (z w : ℂ) :
    Complex.normSq (star z - w) =
      Complex.normSq z + Complex.normSq w - 2 * (z * w).re := by
  simp only [Complex.normSq_apply, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.mul_re]
  ring

/- The substantive scalar certificate. Uniform modulus and the projected
   cubic recurrence imply alpha² = alpha + |mu|². Since alpha+beta=1,
   alpha*beta + |mu|² vanishes. -/
private theorem no_split_of_projected_cubic {d : ℕ} [NeZero d]
    (a b : Fin d → ℂ) (alpha beta : ℝ) (mu : ℂ)
    (haZero : ∑ i, a i = 0)
    (hAlpha : 0 ≤ alpha) (hBeta : 0 ≤ beta)
    (hMass : alpha + beta = 1)
    (haNorm : ∀ i, Complex.normSq (a i) = alpha)
    (hbMass : ∑ i, Complex.normSq (b i) = (d : ℝ) * beta)
    (hCubic : ∀ i, a i * a i + mu = star (a i)) :
    (∀ i, a i = 0) ∨ (∀ i, b i = 0) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hPoint : ∀ i, alpha ^ 2 =
      alpha + Complex.normSq mu - 2 * (a i * mu).re := by
    intro i
    have hRec : a i * a i = star (a i) - mu := by
      linear_combination hCubic i
    calc
      alpha ^ 2 = Complex.normSq (a i * a i) := by
        rw [Complex.normSq_mul, haNorm i]
        ring
      _ = Complex.normSq (star (a i) - mu) := congrArg Complex.normSq hRec
      _ = alpha + Complex.normSq mu - 2 * (a i * mu).re := by
        rw [normSq_star_sub, haNorm i]
  have hCross : (∑ i, (a i * mu).re) = 0 := by
    rw [← Complex.re_sum, ← Finset.sum_mul, haZero, zero_mul]
    rfl
  have hSum : (d : ℝ) * alpha ^ 2 =
      (d : ℝ) * (alpha + Complex.normSq mu) := by
    calc
      (d : ℝ) * alpha ^ 2 = ∑ _i : Fin d, alpha ^ 2 := by simp
      _ = ∑ i : Fin d, (alpha + Complex.normSq mu - 2 * (a i * mu).re) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hPoint i
      _ = (d : ℝ) * (alpha + Complex.normSq mu) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hCross]
        simp
  have hScalar : alpha ^ 2 = alpha + Complex.normSq mu :=
    mul_left_cancel₀ hd hSum
  have hCertificate : alpha * beta + Complex.normSq mu = 0 := by
    nlinarith
  have hProduct : alpha * beta = 0 := by
    nlinarith [Complex.normSq_nonneg mu, mul_nonneg hAlpha hBeta]
  rcases mul_eq_zero.mp hProduct with hA | hB
  · left
    intro i
    apply Complex.normSq_eq_zero.mp
    rw [haNorm i, hA]
  · right
    have hSumB : ∑ i, Complex.normSq (b i) = 0 := by
      rw [hbMass, hB, mul_zero]
    intro i
    have hLe : Complex.normSq (b i) ≤ ∑ j, Complex.normSq (b j) :=
      Finset.single_le_sum (fun j _ ↦ Complex.normSq_nonneg (b j)) (Finset.mem_univ i)
    apply Complex.normSq_eq_zero.mp
    exact le_antisymm (by simpa [hSumB] using hLe) (Complex.normSq_nonneg (b i))

/-- An order-three unitary cannot have nonzero trace-zero components in both
of two mutually unbiased diagonal contexts. The orthogonality arguments are
exactly the projective-measurement laws already used by the context API.

This rules out a balanced equality case of the two-context symmetry budget.
It does not assert any strict-X completion affinity lower bound. -/
theorem orderThree_complementary_contexts_no_split
    {d : ℕ} [NeZero d]
    (C D : RankOneContext d)
    (hC : ∀ i j, i ≠ j → C.projector i * C.projector j = 0)
    (hD : ∀ i j, i ≠ j → D.projector i * D.projector j = 0)
    (hMUB : ∀ i j, overlap C D i j = (d : ℝ)⁻¹)
    (a b : Fin d → ℂ)
    (haZero : ∑ i, a i = 0) (hbZero : ∑ i, b i = 0)
    (hUnitary :
      ((∑ i, a i • C.projector i) + (∑ j, b j • D.projector j)) *
        ((∑ i, a i • C.projector i) + (∑ j, b j • D.projector j))ᴴ = 1)
    (hOrderThree :
      ((∑ i, a i • C.projector i) + (∑ j, b j • D.projector j)) ^ 3 = 1) :
    (∀ i, a i = 0) ∨ (∀ j, b j = 0) := by
  let S := diagonalElement C a + diagonalElement D b
  let beta : ℝ := (∑ j, Complex.normSq (b j)) / (d : ℝ)
  let alpha : ℝ := 1 - beta
  let mu : ℂ := (d : ℂ)⁻¹ * ∑ j, b j * b j
  have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hCD := complex_overlap_of_real_overlap C D hMUB
  have hbStar : ∑ j, star (b j) = 0 := by
    simpa using congrArg (starRingEnd ℂ) hbZero
  have hAdj : Sᴴ = diagonalElement C (fun i ↦ star (a i)) +
      diagonalElement D (fun i ↦ star (b i)) := by
    dsimp [S]
    rw [Matrix.conjTranspose_add, diagonal_adjoint, diagonal_adjoint]
  have hSS : S * Sᴴ = 1 := hUnitary
  have hCube : S ^ 3 = 1 := hOrderThree
  have hSquare : S * S = Sᴴ := by
    calc
      S * S = (S * S) * (S * Sᴴ) := by rw [hSS, Matrix.mul_one]
      _ = S ^ 3 * Sᴴ := by simp only [pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
      _ = Sᴴ := by rw [hCube, Matrix.one_mul]
  have hBeta : 0 ≤ beta := by
    exact div_nonneg (Finset.sum_nonneg (fun j _ ↦ Complex.normSq_nonneg (b j)))
      (Nat.cast_nonneg d)
  have hbMass : ∑ j, Complex.normSq (b j) = (d : ℝ) * beta := by
    dsimp [beta]
    field_simp [hdReal]
  have haNorm : ∀ i, Complex.normSq (a i) = alpha := by
    intro i
    have hDiag : trace (C.projector i * (S * Sᴴ)) = 1 := by
      rw [hSS, Matrix.mul_one, (C.rankOne i).2.2.1]
    rw [hAdj] at hDiag
    change trace (C.projector i *
      ((diagonalElement C a + diagonalElement D b) *
        (diagonalElement C (fun j ↦ star (a j)) +
          diagonalElement D (fun j ↦ star (b j))))) = 1 at hDiag
    rw [trace_projector_product_of_sums C D hC hD hCD
      a b (fun j ↦ star (a j)) (fun j ↦ star (b j)) hbZero hbStar] at hDiag
    simp only [Complex.star_def, Complex.mul_conj] at hDiag
    have hReal := congrArg Complex.re hDiag
    have hCast : (d : ℂ)⁻¹ = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by simp
    rw [hCast] at hReal
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_sum, Complex.im_sum, mul_zero, zero_mul,
      sub_zero, Complex.one_re] at hReal
    change Complex.normSq (a i) = 1 - beta
    dsimp [beta]
    simp only [div_eq_mul_inv]
    nlinarith
  have hAlpha : 0 ≤ alpha := by
    rw [← haNorm (0 : Fin d)]
    exact Complex.normSq_nonneg _
  have hCubic : ∀ i, a i * a i + mu = star (a i) := by
    intro i
    have hDiag := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ ↦
      trace (C.projector i * M)) hSquare
    rw [hAdj] at hDiag
    change trace (C.projector i *
      ((diagonalElement C a + diagonalElement D b) *
        (diagonalElement C a + diagonalElement D b))) =
      trace (C.projector i *
        (diagonalElement C (fun j ↦ star (a j)) +
          diagonalElement D (fun j ↦ star (b j)))) at hDiag
    rw [trace_projector_product_of_sums C D hC hD hCD a b a b hbZero hbZero,
      Matrix.mul_add, Matrix.trace_add,
      trace_projector_diagonal C hC,
      trace_projector_other_diagonal C D hCD,
      hbStar, mul_zero, add_zero] at hDiag
    exact hDiag
  exact no_split_of_projected_cubic a b alpha beta mu haZero hAlpha hBeta
    (by dsimp [alpha]; ring) haNorm hbMass hCubic

#print axioms orderThree_complementary_contexts_no_split

end D5.S3.Quantum.Tomography.OrderThreeComplementaryContextRigidity
