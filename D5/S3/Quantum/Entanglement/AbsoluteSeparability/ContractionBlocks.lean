/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite phase decompositions of contractions yield separable Hermitian scalar shifts. -/

import Mathlib
import D5.S3.Resource.EntanglementWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks

open Matrix
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open scoped Kronecker ComplexOrder MatrixOrder

private noncomputable def circlePhase (x : ℝ) : ℂ :=
  ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I)

private lemma phase_denominator_ne_zero (x : ℝ) : (x : ℂ) + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

private lemma circlePhase_norm (x : ℝ) : ‖circlePhase x‖ = 1 := by
  have hn : ‖(x : ℂ) - Complex.I‖ = ‖(x : ℂ) + Complex.I‖ := by
    have he : (starRingEnd ℂ) ((x : ℂ) + Complex.I) = (x : ℂ) - Complex.I := by
      simp [sub_eq_add_neg]
    rw [← he, Complex.norm_conj]
  rw [circlePhase, norm_div, hn]
  exact div_self (norm_ne_zero_iff.mpr (phase_denominator_ne_zero x))

private lemma circlePhase_injective : Function.Injective circlePhase := by
  intro x y h
  have hm := (div_eq_div_iff (phase_denominator_ne_zero x)
    (phase_denominator_ne_zero y)).mp h
  have he : (x : ℂ) = y := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    apply (mul_left_cancel₀ hI)
    linear_combination (1 / 2 : ℂ) * hm
  exact Complex.ofReal_injective he

/-- Every finite complex matrix has an invertible scalar pencil at a unit scalar. -/
private theorem exists_unit_phase_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (z • (1 : Matrix ι ι ℂ) - C).det ≠ 0 := by
  classical
  let f : Fin (Fintype.card ι + 1) → ℂ := fun k => circlePhase (k.val : ℝ)
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    exact_mod_cast circlePhase_injective h
  have hex : ∃ i, C.charpoly.eval (f i) ≠ 0 := by
    by_contra h
    have hz : C.charpoly = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero C.charpoly hf
        (by simpa using h) (by simp)
    exact C.charpoly_monic.ne_zero hz
  obtain ⟨i, hi⟩ := hex
  refine ⟨f i, circlePhase_norm _, ?_⟩
  have he : Matrix.scalar ι (f i) = f i • (1 : Matrix ι ι ℂ) := by
    ext a b
    simp [Matrix.scalar, Matrix.diagonal, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, mul_ite]
  rwa [Matrix.eval_charpoly, he] at hi

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
  obtain ⟨z, hz, hdet⟩ := exists_unit_phase_det_ne_zero U
  have hzn : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  let B : Matrix ι ι ℂ := z⁻¹ • U
  let D : Matrix ι ι ℂ := 1 - B
  have hs : star (z⁻¹) * z⁻¹ = (1 : ℂ) := by
    change (starRingEnd ℂ) (z⁻¹) * z⁻¹ = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_inv, hz]
    norm_num
  have hUU : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
  have hB : Bᴴ * B = 1 := by
    simp only [B, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hUU]
    rw [mul_comm, hs, one_smul]
  have hscale : z • D = z • (1 : Matrix ι ι ℂ) - U := by
    simp [D, B, smul_sub, smul_smul, hzn]
  have hDn : D.det ≠ 0 := by
    intro h
    apply hdet
    rw [← hscale, Matrix.det_smul, h, mul_zero]
  have hDu : IsUnit D.det := isUnit_iff_ne_zero.mpr hDn
  have hDl := Matrix.nonsing_inv_mul D hDu
  have hDr := Matrix.mul_nonsing_inv D hDu
  let A : Matrix ι ι ℂ := Complex.I • ((1 + B) * D⁻¹)
  have hAD : A * D = Complex.I • (1 + B) := by
    simp only [A, smul_mul_assoc, mul_assoc, hDl, mul_one]
  have hmid : Dᴴ * A * D = Complex.I • (B - Bᴴ) := by
    rw [mul_assoc, hAD, Matrix.mul_smul]
    congr 1
    simp only [D, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    noncomm_ring [hB]
  have hmidH : (Complex.I • (B - Bᴴ)).IsHermitian := by
    change (Complex.I • (B - Bᴴ))ᴴ = _
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    simp only [RCLike.star_def, Complex.conj_I]
    module
  have hA : A.IsHermitian := by
    rw [← hmid] at hmidH
    have h := Matrix.isHermitian_conjTranspose_mul_mul D⁻¹ hmidH
    have he : D⁻¹ᴴ * (Dᴴ * A * D) * D⁻¹ = A := by
      calc
        _ = (D * D⁻¹)ᴴ * A * (D * D⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = A := by rw [hDr]; simp
    rwa [he] at h
  let v : ι → ι → ℂ := fun r => ⇑(hA.eigenvectorBasis r)
  let t : ι → ℝ := hA.eigenvalues
  have hcomplete : (∑ r, vecMulVec (v r) (star (v r))) = 1 := by
    have h := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    ext i j
    simpa only [v, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Matrix.mul_apply, Unitary.coe_star, Matrix.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using
      congrArg (fun M : Matrix ι ι ℂ => M i j) h
  have hspectral : ∑ r, (t r : ℂ) • vecMulVec (v r) (star (v r)) = A := by
    conv_rhs => rw [hA.spectral_theorem]
    ext i j
    simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Matrix.star_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
      Matrix.sum_apply, Matrix.smul_apply, v, t, Matrix.vecMulVec_apply,
      Pi.star_apply, smul_eq_mul, RCLike.ofReal_eq_complex_ofReal]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  let d : ι → ℂ := fun r => ((t r : ℂ) - Complex.I) / ((t r : ℂ) + Complex.I)
  let K : Matrix ι ι ℂ := ∑ r, d r • vecMulVec (v r) (star (v r))
  have hAB : (A + Complex.I • 1) * B = A - Complex.I • 1 := by
    have h := hAD
    simp only [D, Matrix.mul_sub, Matrix.mul_one, smul_add] at h
    simp only [add_mul, smul_mul_assoc, one_mul]
    ext i j
    have he := congrArg (fun M : Matrix ι ι ℂ => M i j) h
    simp only [Matrix.sub_apply, Matrix.add_apply] at he ⊢
    linear_combination -he
  have heig : ∀ r, A * vecMulVec (v r) (star (v r)) =
      (t r : ℂ) • vecMulVec (v r) (star (v r)) := by
    intro r
    rw [Matrix.mul_vecMulVec]
    have h := hA.mulVec_eigenvectorBasis r
    rw [h]
    ext i j
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.real_smul]
    ring
  have hAK : (A + Complex.I • 1) * K = A - Complex.I • 1 := by
    have hd : ∀ r, d r * ((t r : ℂ) + Complex.I) = (t r : ℂ) - Complex.I := by
      intro r
      exact div_mul_cancel₀ _ (phase_denominator_ne_zero _)
    change (A + Complex.I • 1) *
      (∑ r, d r • vecMulVec (v r) (star (v r))) = A - Complex.I • 1
    rw [Finset.mul_sum]
    calc
      _ = ∑ r, ((t r : ℂ) - Complex.I) • vecMulVec (v r) (star (v r)) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Matrix.mul_smul, add_mul, heig, smul_mul_assoc, one_mul,
          ← add_smul, smul_smul, hd]
      _ = A - Complex.I • 1 := by
        simp only [sub_smul, Finset.sum_sub_distrib, hspectral,
          ← Finset.smul_sum, hcomplete]
  have hplus : (A + Complex.I • 1) * D = (2 * Complex.I) • 1 := by
    rw [add_mul, hAD, smul_mul_assoc, one_mul, ← smul_add]
    simp only [D]
    module
  have hplus' : A + Complex.I • 1 = (2 * Complex.I) • D⁻¹ := by
    have h := congrArg (fun M : Matrix ι ι ℂ => M * D⁻¹) hplus
    simpa only [mul_assoc, hDr, mul_one, smul_mul_assoc, one_mul] using h
  have hinj : Function.Injective (fun X : Matrix ι ι ℂ => (A + Complex.I • 1) * X) := by
    apply Matrix.mul_right_injective_of_inv ((2 * Complex.I)⁻¹ • D)
    rw [hplus', smul_mul_smul_comm, hDr, inv_mul_cancel₀]
    · exact one_smul _ _
    · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hKB : K = B := hinj (hAK.trans hAB.symm)
  refine ⟨v, fun r => z * d r, ?_, hcomplete, ?_⟩
  · intro r
    rw [norm_mul, hz]
    exact one_mul _ |>.trans (circlePhase_norm (t r))
  · simp only [mul_smul, ← Finset.smul_sum]
    change z • K = U
    rw [hKB]
    simp [B, smul_smul, hzn]

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
  fun i j =>
    if i.1 = 0 then
      if j.1 = 0 then (if i.2 = j.2 then 1 else 0) else C i.2 j.2
    else
      if j.1 = 0 then Cᴴ i.2 j.2 else (if i.2 = j.2 then 1 else 0)

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
    · simpa [pairBlock, phaseVector, hcc, Matrix.of_apply, Matrix.sum_apply,
        Matrix.one_apply,
        Matrix.kroneckerMap,
        Matrix.kroneckerMap_apply,
        Matrix.vecMulVec_apply, Finset.sum_apply] using
        (congrArg (fun M => M p q) hI).symm
    · simpa [pairBlock, phaseVector, Matrix.of_apply, Matrix.sum_apply,
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
      simpa [pairBlock, phaseVector, Matrix.of_apply, Matrix.sum_apply,
        Matrix.one_apply,
        Matrix.kroneckerMap,
        Matrix.kroneckerMap_apply,
        Matrix.vecMulVec_apply, Finset.sum_apply] using
        (congrArg (fun M => M p q) hCstar)
    · simpa [pairBlock, phaseVector, hcc', Matrix.of_apply, Matrix.sum_apply,
        Matrix.one_apply,
        Matrix.kroneckerMap,
        Matrix.kroneckerMap_apply,
        Matrix.vecMulVec_apply, Finset.sum_apply] using
        (congrArg (fun M => M p q) hI).symm

private def block {m n : ℕ}
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (i j : Fin m) :
    Matrix (Fin n) (Fin n) ℂ := fun p q => H (i, p) (j, q)

private def embedVector {m n : ℕ} (i : Fin m) (x : Fin n → ℂ) :
    Fin m × Fin n → ℂ := fun ap => if ap.1 = i then x ap.2 else 0

private lemma block_contraction {m n : ℕ}
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hH : ∀ x : Fin m × Fin n → ℂ,
      ‖WithLp.toLp 2 (H *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖) (i j : Fin m) :
    ∀ x : Fin n → ℂ,
      ‖WithLp.toLp 2 (block H i j *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  intro x
  have he : ∀ p, (H *ᵥ embedVector j x) (i, p) = (block H i j *ᵥ x) p := by
    intro p
    simp [mulVec, dotProduct, Fintype.sum_prod_type, embedVector, block]
  have hn : ‖WithLp.toLp 2 (embedVector j x)‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, embedVector,
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

private lemma separableCone_sum {m n : ℕ} {ι : Type*} [Fintype ι]
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
    injectPair, pairBlock, Matrix.one_apply]
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

#print axioms contraction_decomposition
#print axioms separableCone_scalar_add_of_opNorm_le_one

end D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
