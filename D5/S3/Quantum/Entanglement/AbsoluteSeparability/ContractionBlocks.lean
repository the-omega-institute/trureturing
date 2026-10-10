/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite phase decompositions of contractions yield separable Hermitian scalar shifts. -/

import Mathlib
import D5.S3.Resource.EntanglementWitness
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks

open Matrix
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open scoped Kronecker ComplexOrder MatrixOrder

private theorem exists_unitary_dilation {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (hC : (1 - Cᴴ * C).PosSemidef) :
    ∃ U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ,
      U ∈ Matrix.unitaryGroup _ ℂ ∧ ∀ i j, U (Sum.inl i) (Sum.inl j) = C i j := by
  classical
  let R := CFC.sqrt (1 - Cᴴ * C)
  have hR : R.IsHermitian := (CFC.sqrt_nonneg (1 - Cᴴ * C)).posSemidef.isHermitian
  have hRR : Rᴴ * R = 1 - Cᴴ * C := by
    rw [hR.eq]
    exact CFC.sqrt_mul_sqrt_self _ hC.nonneg
  let v : (Fin n ⊕ Fin n) → EuclideanSpace ℂ (Fin n ⊕ Fin n) :=
    Sum.elim (fun j => WithLp.toLp 2 (Sum.elim (fun i => C i j) (fun i => R i j)))
      (fun _ => 0)
  let s : Set (Fin n ⊕ Fin n) := Set.range Sum.inl
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    obtain ⟨i, rfl⟩ := hi
    obtain ⟨j, rfl⟩ := hj
    have hsum : Cᴴ * C + Rᴴ * R = 1 := by rw [hRR]; abel
    have hm := congrArg (fun M => M i j) hsum
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] at hm
    simpa [Set.domRestrict_apply, v, PiLp.inner_apply, Fintype.sum_sum_type,
      Subtype.ext_iff, Sum.elim_inl, Sum.elim_inr, mul_comm] using hm
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp)
  let U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    (EuclideanSpace.basisFun (Fin n ⊕ Fin n) ℂ).toBasis.toMatrix b
  refine ⟨U, (EuclideanSpace.basisFun _ ℂ).toMatrix_orthonormalBasis_mem_unitary b, ?_⟩
  intro i j
  have he := hb (Sum.inl j) (by exact ⟨j, rfl⟩)
  change (b (Sum.inl j)) (Sum.inl i) = C i j
  simpa only [v, Sum.elim_inl] using
    congrArg (fun w => w (Sum.inl i)) he

private theorem unitary_phase_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    ∃ (v : ι → ι → ℂ) (c : ι → ℂ), (∀ r, ‖c r‖ = 1) ∧
      (∑ r, vecMulVec (v r) (star (v r))) = 1 ∧
      (∑ r, c r • vecMulVec (v r) (star (v r))) = U := by
  classical
  let : IsStarNormal U := ⟨by
    change star U * U = U * star U
    exact (Unitary.star_mul_self_of_mem hU).trans
      (Unitary.mul_star_self_of_mem hU).symm⟩
  obtain ⟨Q, hQ, c, hc⟩ := Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal U
  have he : U = Q * Matrix.diagonal c * Qᴴ := by
    calc
      U = (Q * star Q) * U * (Q * star Q) := by
        rw [Unitary.mul_star_self_of_mem hQ]
        simp
      _ = Q * (star Q * U * Q) * star Q := by simp only [Matrix.mul_assoc]
      _ = Q * Matrix.diagonal c * Qᴴ := by rw [hc]; rfl
  refine ⟨fun r i => Q i r, c, ?_, ?_, ?_⟩
  · intro r
    have hd : Matrix.diagonal c ∈ Matrix.unitaryGroup ι ℂ := by
      rw [← hc]
      exact mul_mem (mul_mem (Unitary.star_mem hQ) hU) hQ
    have hh := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hd) r) r
    have hz : star (c r) * c r = 1 := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
        starRingEnd_apply, Pi.star_apply] using hh
    have hn := congrArg norm hz
    rw [norm_mul, norm_star, norm_one] at hn
    nlinarith [norm_nonneg (c r)]
  · ext i j
    simpa only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Matrix.mul_apply, Matrix.star_apply] using
      congrArg (fun M : Matrix ι ι ℂ => M i j) (Unitary.mul_star_self_of_mem hQ)
  · rw [he]
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Pi.star_apply, smul_eq_mul, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    apply Finset.sum_congr rfl
    intro r hr
    ring

/-- A Euclidean contraction is a compression of a finite rank-one phase decomposition. -/
theorem contraction_decomposition {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (hC : (1 - Cᴴ * C).PosSemidef) :
    ∃ (a : (Fin n ⊕ Fin n) → Fin n → ℂ) (c : (Fin n ⊕ Fin n) → ℂ),
      (∀ r, ‖c r‖ = 1) ∧
      (∑ r, vecMulVec (a r) (star (a r))) = 1 ∧
      (∑ r, c r • vecMulVec (a r) (star (a r))) = C := by
  classical
  obtain ⟨U, hU, hUC⟩ := exists_unitary_dilation C hC
  obtain ⟨v, c, hc, hI, hv⟩ := unitary_phase_decomposition U hU
  refine ⟨fun r i => v r (Sum.inl i), c, hc, ?_, ?_⟩
  · ext i j
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.one_apply] using
      congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hI
  · ext i j
    simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, hUC] using
      congrArg (fun M => M (Sum.inl i) (Sum.inl j)) hv

private lemma contraction_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ)
    (hC : ∀ x : ι → ℂ, ‖WithLp.toLp 2 (C *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖) :
    (1 - Cᴴ * C).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_one.sub (isHermitian_conjTranspose_mul_self C))
  intro x
  have hs (y : ι → ℂ) : star y ⬝ᵥ y = (‖WithLp.toLp 2 y‖ ^ 2 : ℝ) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp,
      inner_self_eq_norm_sq_to_K]
    simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]
  have he : star x ⬝ᵥ ((1 - Cᴴ * C) *ᵥ x) =
      ((‖WithLp.toLp 2 x‖ ^ 2 - ‖WithLp.toLp 2 (C *ᵥ x)‖ ^ 2 : ℝ) : ℂ) := by
    rw [sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec,
      dotProduct_mulVec, ← star_mulVec, hs, hs, Complex.ofReal_sub]
  rw [he, Complex.zero_le_real]
  exact sub_nonneg.mpr (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (hC x))

private lemma one_add_posSemidef_of_contraction {ι : Type*} [Fintype ι]
    [DecidableEq ι] (C : Matrix ι ι ℂ) (hH : C.IsHermitian)
    (hC : (1 - Cᴴ * C).PosSemidef) : (1 + C).PosSemidef := by
  have hp := (posSemidef_conjTranspose_mul_self (1 + C)).add hC
  have he : (1 + C)ᴴ * (1 + C) + (1 - Cᴴ * C) = (2 : ℝ) • (1 + C) := by
    rw [conjTranspose_add, conjTranspose_one, hH.eq, two_smul ℝ]
    noncomm_ring
  have h := hp.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  simpa only [he, smul_smul, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    one_smul] using h

private def pairBlock {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ :=
  (Matrix.fromBlocks 1 C Cᴴ 1).submatrix
    (fun i => if i.1 = 0 then Sum.inl i.2 else Sum.inr i.2)
    (fun j => if j.1 = 0 then Sum.inl j.2 else Sum.inr j.2)

private def phaseVector (z : ℂ) : Fin 2 → ℂ := fun i =>
  if i = 0 then 1 else star z

/- A finite rank-one phase decomposition is exactly the algebraic input used by
the middle-ray construction.  The contraction lemma supplies this input. -/
private theorem pair_block_separable_of_decomposition {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℂ)
    (a : Fin k → Fin n → ℂ) (c : Fin k → ℂ)
    (hc : ∀ r, ‖c r‖ = 1)
    (hI : ∑ r, vecMulVec (a r) (star (a r)) = 1)
    (hC : ∑ r, c r • vecMulVec (a r) (star (a r)) = C) :
    separableCone (pairBlock C) := by
  have hcc : ∀ r, star (c r) * c r = (1 : ℂ) := by
    intro r
    change (starRingEnd ℂ) (c r) * c r = (1 : ℂ)
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc r]
    norm_num
  have hcc' : ∀ r, (starRingEnd ℂ) (c r) * c r = (1 : ℂ) := by
    intro r
    simpa only [starRingEnd_apply] using hcc r
  refine ⟨k, (fun r => vecMulVec (phaseVector (c r)) (star (phaseVector (c r)))),
    (fun r => vecMulVec (a r) (star (a r))), ?_, ?_⟩
  · intro r
    exact ⟨posSemidef_vecMulVec_self_star _, posSemidef_vecMulVec_self_star _⟩
  · ext i j
    rcases i with ⟨i, p⟩
    rcases j with ⟨j, q⟩
    fin_cases i <;> fin_cases j
    · simpa [pairBlock, Matrix.fromBlocks, Matrix.submatrix, phaseVector, hcc,
        Matrix.of_apply, Matrix.sum_apply,
        Matrix.one_apply,
        Matrix.kroneckerMap,
        Matrix.kroneckerMap_apply,
        Matrix.vecMulVec_apply, Finset.sum_apply] using
        (congrArg (fun M => M p q) hI).symm
    · simpa [pairBlock, Matrix.fromBlocks, Matrix.submatrix, phaseVector,
        Matrix.of_apply, Matrix.sum_apply,
        Matrix.one_apply,
        Matrix.kroneckerMap,
        Matrix.kroneckerMap_apply,
        Matrix.vecMulVec_apply, Finset.sum_apply] using
        (congrArg (fun M => M p q) hC).symm
    · have hCstar : Cᴴ = ∑ r, (star (c r)) • vecMulVec (a r) (star (a r)) := by
        rw [← hC]
        rw [Matrix.conjTranspose_sum]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec]
        ext p q
        simp [Matrix.vecMulVec_apply]
      simpa [pairBlock, Matrix.fromBlocks, Matrix.submatrix, phaseVector,
        Matrix.of_apply, Matrix.sum_apply,
        Matrix.one_apply,
        Matrix.kroneckerMap,
        Matrix.kroneckerMap_apply,
        Matrix.vecMulVec_apply, Finset.sum_apply] using
        (congrArg (fun M => M p q) hCstar)
    · simpa [pairBlock, Matrix.fromBlocks, Matrix.submatrix, phaseVector, hcc',
        Matrix.of_apply, Matrix.sum_apply,
        Matrix.one_apply,
        Matrix.kroneckerMap,
        Matrix.kroneckerMap_apply,
        Matrix.vecMulVec_apply, Finset.sum_apply] using
        (congrArg (fun M => M p q) hI).symm

private def block {m n : ℕ}
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (i j : Fin m) :
    Matrix (Fin n) (Fin n) ℂ := H.submatrix (fun p => (i, p)) (fun q => (j, q))

private def embedVector {m n : ℕ} (i : Fin m) (x : Fin n → ℂ) :
    Fin m × Fin n → ℂ := fun ap => (Pi.single i x : Fin m → Fin n → ℂ) ap.1 ap.2

private lemma block_contraction {m n : ℕ}
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hH : ∀ x : Fin m × Fin n → ℂ,
      ‖WithLp.toLp 2 (H *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖) (i j : Fin m) :
    ∀ x : Fin n → ℂ,
      ‖WithLp.toLp 2 (block H i j *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  intro x
  have he : ∀ p, (H *ᵥ embedVector j x) (i, p) = (block H i j *ᵥ x) p := by
    intro p
    simp [mulVec, dotProduct, Fintype.sum_prod_type, embedVector, Pi.single_apply, ite_apply, block]
  have hn : ‖WithLp.toLp 2 (embedVector j x)‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, embedVector, Pi.single_apply, ite_apply,
      apply_ite, Finset.sum_ite_irrel]
  have hle : ‖WithLp.toLp 2 (block H i j *ᵥ x)‖ ^ 2 ≤
      ‖WithLp.toLp 2 (H *ᵥ embedVector j x)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    rw [← funext he]
    exact Finset.single_le_sum
      (f := fun a => ∑ p, ‖(H *ᵥ embedVector j x) (a, p)‖ ^ 2)
      (fun a _ => Finset.sum_nonneg (fun p _ => sq_nonneg _)) (Finset.mem_univ i)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    _ ≤ ‖WithLp.toLp 2 (H *ᵥ embedVector j x)‖ ^ 2 := hle
    _ ≤ ‖WithLp.toLp 2 (embedVector j x)‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hH _)
    _ = _ := hn

lemma separableCone_sum {m n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hf : ∀ i, separableCone (f i)) : separableCone (∑ i, f i) := by
  classical
  have hs (s : Finset ι) : separableCone (∑ i ∈ s, f i) := by
    induction s using Finset.induction_on with
    | empty => simpa using (separableCone_zero (m := m) (n := n))
    | @insert i s hi ih =>
      simpa [Finset.sum_insert, hi] using separableCone_add (hf i) ih
  simpa using hs Finset.univ

private lemma pair_block_separable {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (hC : (1 - Cᴴ * C).PosSemidef) : separableCone (pairBlock C) := by
  classical
  obtain ⟨a, c, hc, hI, ha⟩ := contraction_decomposition C hC
  let e : Fin (Fintype.card (Fin n ⊕ Fin n)) ≃ (Fin n ⊕ Fin n) :=
    (Fintype.equivFin _).symm
  apply pair_block_separable_of_decomposition C (fun r => a (e r)) (fun r => c (e r))
  · exact fun r => hc (e r)
  · exact (e.sum_comp (fun r => vecMulVec (a r) (star (a r)))).trans hI
  · exact (e.sum_comp (fun r => c r • vecMulVec (a r) (star (a r)))).trans ha

private def injectPair {m : ℕ} (i j : Fin m) : Matrix (Fin m) (Fin 2) ℂ :=
  fun x u => if u = 0 then (if x = i then 1 else 0) else (if x = j then 1 else 0)

private def embeddedPair {m n : ℕ} (i j : Fin m) (C : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (injectPair i j ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * pairBlock C *
    (injectPair i j ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ

private lemma embeddedPair_separable {m n : ℕ} (i j : Fin m)
    (C : Matrix (Fin n) (Fin n) ℂ) (hC : (1 - Cᴴ * C).PosSemidef) :
    separableCone (embeddedPair i j C) := by
  classical
  obtain ⟨k, A, B, hAB, he⟩ := pair_block_separable C hC
  refine ⟨k, fun r => injectPair i j * A r * (injectPair i j)ᴴ, B, ?_, ?_⟩
  · intro r
    exact ⟨(hAB r).1.mul_mul_conjTranspose_same _, (hAB r).2⟩
  · simp only [embeddedPair, he, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp

set_option maxHeartbeats 1000000 in
-- Expanding two finite block products requires additional normalization steps.
private lemma embeddedPair_apply {m n : ℕ} (i j x y : Fin m)
    (C : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    embeddedPair i j C (x, p) (y, q) =
      (if x = i ∧ y = i then (1 : Matrix (Fin n) (Fin n) ℂ) p q else 0) +
      (if x = j ∧ y = j then (1 : Matrix (Fin n) (Fin n) ℂ) p q else 0) +
      (if x = i ∧ y = j then C p q else 0) +
      (if x = j ∧ y = i then Cᴴ p q else 0) := by
  classical
  simp [embeddedPair, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply,
    injectPair, pairBlock, Matrix.fromBlocks, Matrix.submatrix, Matrix.one_apply]
  split_ifs <;> simp_all <;> ring

private def diagonalTerm {m n : ℕ}
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (i : Fin m) :=
  vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))) ⊗ₖ (1 + block H i i)

private lemma sum_except {m : ℕ} (x : Fin m) (z : ℂ) :
    ∑ i : Fin m, (if i = x then 0 else z) = (m : ℂ) * z - z := by
  calc
    _ = (∑ _i : Fin m, z) - ∑ i : Fin m, (if i = x then z else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp
    _ = _ := by simp [nsmul_eq_mul]

set_option maxHeartbeats 1000000 in
-- The entry calculation separates the finite diagonal and off-diagonal cases.
private lemma middle_block_identity {m n : ℕ}
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hH : H.IsHermitian) :
    (m : ℂ) • 1 + H = (∑ i, diagonalTerm H i) +
      (1 / 2 : ℝ) • ∑ i : Fin m, ∑ j : Fin m,
        if i = j then 0 else embeddedPair i j (block H i j) := by
  classical
  have hstar (a b : Fin m × Fin n) : (starRingEnd ℂ) (H b a) = H a b :=
    congrArg (fun M => M a b) hH.eq
  ext ⟨x, p⟩ ⟨y, q⟩
  have hd : (∑ i, diagonalTerm H i) (x, p) (y, q) =
      if x = y then (1 : Matrix (Fin n) (Fin n) ℂ) p q + H (x, p) (y, q) else 0 := by
    by_cases hxy : x = y
    · subst y
      simp [diagonalTerm, Matrix.sum_apply, Matrix.kroneckerMap_apply,
        Matrix.vecMulVec_apply, Pi.single_apply, block, Matrix.add_apply]
    · simp [diagonalTerm, Matrix.sum_apply, Matrix.kroneckerMap_apply,
        Matrix.vecMulVec_apply, Pi.single_apply, block, hxy]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, hd,
    Complex.real_smul, smul_eq_mul]
  by_cases hxy : x = y
  · subst y
    have hp (i j : Fin m) :
        (if i = j then (0 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
          else embeddedPair i j (block H i j)) (x, p) (x, q) =
        (if i = x then (if j = x then 0 else (1 : Matrix (Fin n) (Fin n) ℂ) p q)
          else 0) +
        (if j = x then (if i = x then 0 else (1 : Matrix (Fin n) (Fin n) ℂ) p q)
          else 0) := by
      by_cases hij : i = j
      · rw [if_pos hij]
        change 0 = _
        subst j
        by_cases hi : i = x <;> simp [hi]
      · rw [if_neg hij, embeddedPair_apply]
        by_cases hi : i = x <;> by_cases hj : j = x <;>
          simp [hi, hj, eq_comm] <;> aesop
    simp only [hp, if_true, Finset.sum_add_distrib, Finset.sum_ite_irrel]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, sum_except,
      Matrix.one_apply, Prod.mk.injEq, true_and]
    split_ifs with hpq
    · simp_all
      ring
    · simp_all
  · have hp (i j : Fin m) :
        (if i = j then (0 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
          else embeddedPair i j (block H i j)) (x, p) (y, q) =
        (if i = x ∧ j = y then H (x, p) (y, q) else 0) +
        (if i = y ∧ j = x then H (x, p) (y, q) else 0) := by
      by_cases hij : i = j
      · rw [if_pos hij]
        change 0 = _
        subst j
        by_cases hix : i = x <;> by_cases hiy : i = y <;>
          simp [hix, hiy] <;> aesop
      · rw [if_neg hij, embeddedPair_apply]
        by_cases hix : i = x <;> by_cases hiy : i = y <;>
          by_cases hjx : j = x <;> by_cases hjy : j = y <;>
          simp [hix, hiy, hjx, hjy, hxy,
            Matrix.conjTranspose_apply, block, hstar, eq_comm] <;> aesop
    simp only [hp, Finset.sum_add_distrib]
    simp [hxy, Prod.mk.injEq, ite_and, Finset.sum_ite_irrel]
    ring

/-- A Hermitian Euclidean contraction has a separable scalar shift by the first dimension. -/
theorem separableCone_scalar_add_of_opNorm_le_one {m n : ℕ}
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hH : H.IsHermitian)
    (hbound : ∀ x : Fin m × Fin n → ℂ,
      ‖WithLp.toLp 2 (H *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖) :
    separableCone ((m : ℂ) • 1 + H) := by
  classical
  rw [middle_block_identity H hH]
  apply separableCone_add
  · apply separableCone_sum
    intro i
    have hi : (block H i i).IsHermitian := by
      ext p q
      exact congrArg (fun M => M (i, p) (i, q)) hH.eq
    have hp := one_add_posSemidef_of_contraction (block H i i) hi
      (contraction_posSemidef _ (block_contraction H hbound i i))
    refine ⟨1, fun _ => vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ))),
      fun _ => 1 + block H i i, fun _ => ⟨posSemidef_vecMulVec_self_star _, hp⟩, ?_⟩
    simp [diagonalTerm]
  · apply separableCone_smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply separableCone_sum
    intro i
    apply separableCone_sum
    intro j
    split_ifs
    · exact separableCone_zero
    · exact embeddedPair_separable i j _
        (contraction_posSemidef _ (block_contraction H hbound i j))

#print axioms separableCone_sum
#print axioms contraction_decomposition
#print axioms separableCone_scalar_add_of_opNorm_le_one

end D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
