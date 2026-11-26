/- GID: D5/S3/Quantum/Semigroups/WuEndpointPauliFrame
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuEndpointPauliFrame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Anticommuting Hermitian involutions give real orthonormal frames and two bounds on sums of complex squared overlaps. -/

import D5.S3.Quantum.Semigroups.WuRankOneEndpointClifford
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Matrix.Hermitian

/-! Real frames for complex symmetric involutions and the Wu sign-flip Pauli words. -/

noncomputable section

open scoped InnerProductSpace BigOperators Matrix Kronecker

namespace WuEndpointPauliFrame

variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The identity slot uses an imaginary phase so it is real-orthogonal to the other slots. -/
def frame (T : J → E →ₗ[ℂ] E) (v : E) : Option J → E :=
  fun j => j.elim (Complex.I • v) (fun i => T i v)

section RealFrame

attribute [local instance] InnerProductSpace.complexToReal

/-- Symmetric anticommuting involutions acting on a unit vector give an orthonormal
family over the reals after rotating the identity slot by `i`. -/
theorem real_orthonormal (T : J → E →ₗ[ℂ] E)
    (hsym : ∀ j, (T j).IsSymmetric) (hsq : ∀ j x, T j (T j x) = x)
    (hanti : ∀ i j, i ≠ j → ∀ x, T i (T j x) = -(T j (T i x)))
    {v : E} (hv : ‖v‖ = 1) : Orthonormal ℝ (frame T v) := by
  refine ⟨?_, ?_⟩
  · intro j
    cases j with
    | none => simp [frame, norm_smul, hv]
    | some j =>
      change ‖T j v‖ = 1
      have h : ‖T j v‖ ^ 2 = ‖v‖ ^ 2 := by
        rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
          hsym j v (T j v), hsq,
          ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h |>.trans hv
  · have hFirst (j : J) : ⟪Complex.I • v, T j v⟫_ℝ = 0 := by
      rw [real_inner_eq_re_inner ℂ, inner_smul_left]
      change ((star (Complex.I) * ⟪v, T j v⟫_ℂ) : ℂ).re = 0
      have hi : (⟪v, T j v⟫_ℂ).im = 0 := (hsym j).im_inner_self_apply v
      simp [Complex.mul_re, hi]
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hFirst j
    | some i =>
      cases j with
      | none =>
        change ⟪T i v, Complex.I • v⟫_ℝ = 0
        rw [real_inner_comm]
        exact hFirst i
      | some j =>
        have hne : i ≠ j := fun h => hij (congrArg some h)
        change ⟪T i v, T j v⟫_ℝ = 0
        rw [real_inner_eq_re_inner ℂ]
        have hneg : ⟪T i v, T j v⟫_ℂ = -⟪T j v, T i v⟫_ℂ := by
          rw [hsym i v (T j v), hanti i j hne, inner_neg_right, ← hsym j v (T i v)]
        have hre : (⟪T i v, T j v⟫_ℂ).re = (⟪T j v, T i v⟫_ℂ).re :=
          inner_re_symm (𝕜 := ℂ) _ _
        have h := congrArg Complex.re hneg
        change (⟪T i v, T j v⟫_ℂ).re = 0
        rw [Complex.neg_re] at h
        linarith only [h, hre]

private theorem complex_bessel_of_real_orthonormal {K : Type*} [Fintype K]
    {w : K → E} (hw : Orthonormal ℝ w) (u : E) :
    ∑ j, ‖⟪u, w j⟫_ℂ‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 := by
  have h₁ := hw.sum_inner_products_le (s := Finset.univ) u
  have h₂ := hw.sum_inner_products_le (s := Finset.univ) (Complex.I • u)
  have hentry (j : K) :
      ‖⟪u, w j⟫_ℂ‖ ^ 2 =
        ‖⟪w j, u⟫_ℝ‖ ^ 2 + ‖⟪w j, Complex.I • u⟫_ℝ‖ ^ 2 := by
    rw [norm_inner_symm, Complex.sq_norm, Complex.normSq_apply,
      real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, inner_smul_right]
    change _ = |(⟪w j, u⟫_ℂ).re| ^ 2 + |(Complex.I * ⟪w j, u⟫_ℂ).re| ^ 2
    simp [Complex.mul_re, pow_two]
  simp_rw [hentry]
  rw [Finset.sum_add_distrib]
  simpa [norm_smul, two_mul] using add_le_add h₁ h₂

end RealFrame

private theorem overlap_le_of_unit [Fintype J] (T : J → E →ₗ[ℂ] E)
    (hsym : ∀ j, (T j).IsSymmetric) (hsq : ∀ j x, T j (T j x) = x)
    (hanti : ∀ i j, i ≠ j → ∀ x, T i (T j x) = -(T j (T i x)))
    (u : E) {v : E} (hv : ‖v‖ = 1) :
    ‖⟪u, v⟫_ℂ‖ ^ 2 + ∑ j, ‖⟪u, T j v⟫_ℂ‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 := by
  simpa [Fintype.sum_option, frame, inner_smul_right, norm_mul] using
    complex_bessel_of_real_orthonormal (real_orthonormal T hsym hsq hanti hv) u

/-- The complex squared-overlap bound associated to the real orthonormal frame.
The input vectors can have arbitrary norms, including zero. -/
theorem overlap_le [Fintype J] (T : J → E →ₗ[ℂ] E)
    (hsym : ∀ j, (T j).IsSymmetric) (hsq : ∀ j x, T j (T j x) = x)
    (hanti : ∀ i j, i ≠ j → ∀ x, T i (T j x) = -(T j (T i x)))
    (u v : E) :
    ‖⟪u, v⟫_ℂ‖ ^ 2 + ∑ j, ‖⟪u, T j v⟫_ℂ‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  by_cases hz : v = 0
  · simp [hz]
  let c : ℂ := (‖v‖ : ℂ)
  let v' : E := c⁻¹ • v
  have hn : ‖c‖ = ‖v‖ := Complex.norm_of_nonneg (norm_nonneg _)
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hc : c ≠ 0 := norm_ne_zero_iff.mp (hn ▸ hvn)
  have hv' : ‖v'‖ = 1 := by
    rw [show v' = c⁻¹ • v from rfl, norm_smul, norm_inv, hn, inv_mul_cancel₀ hvn]
  have hv : v = c • v' := by simp [v', smul_smul, hc]
  calc
    _ = ‖v‖ ^ 2 * (‖⟪u, v'⟫_ℂ‖ ^ 2 + ∑ j, ‖⟪u, T j v'⟫_ℂ‖ ^ 2) := by
      conv_lhs => rw [hv]
      simp only [map_smul, inner_smul_right, norm_mul, hn, mul_pow, ← Finset.mul_sum, ← mul_add]
    _ ≤ ‖v‖ ^ 2 * (2 * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (overlap_le_of_unit T hsym hsq hanti u hv') (sq_nonneg _)
    _ = _ := by ring

#print axioms real_orthonormal
#print axioms overlap_le

end WuEndpointPauliFrame

namespace WuRankOneEndpointFloor

open Matrix
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli pauliMatrix)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (letter_mul letterPhase letterProduct pauli_hermitian)

/-- The Clifford generators in the order of the signed endpoint map. -/
def endpointGamma : Fin 4 → TwoMode :=
  ![pauliWord .I .X, pauliWord .I .Y, pauliWord .X .Z, pauliWord .Y .Z]

/-- The four Pauli conjugations that flip the respective Clifford generators. -/
def endpointU : Fin 4 → TwoMode :=
  ![pauliWord .Z .Y, -pauliWord .Z .X, pauliWord .Y .I, -pauliWord .X .I]

theorem pauliWord_mul (p q r s : Pauli) :
    pauliWord p q * pauliWord r s =
      (letterPhase p r * letterPhase q s) •
        pauliWord (letterProduct p r) (letterProduct q s) := by
  unfold pauliWord
  rw [← Matrix.mul_kronecker_mul, letter_mul p r, letter_mul q s,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]

private theorem pauliWord_one : pauliWord .I .I = 1 := Matrix.one_kronecker_one

theorem endpointU_hermitian (j : Fin 4) : (endpointU j).IsHermitian := by
  fin_cases j <;> simp [Matrix.IsHermitian, endpointU, pauliWord,
    Matrix.conjTranspose_kronecker, pauli_hermitian]

theorem endpointU_sq (j : Fin 4) : endpointU j * endpointU j = 1 := by
  fin_cases j <;> simp [endpointU, pauliWord_mul, letterPhase, letterProduct, pauliWord_one]

theorem endpointU_anticommute (i j : Fin 4) (h : i ≠ j) :
    endpointU i * endpointU j = -(endpointU j * endpointU i) := by
  fin_cases i <;> fin_cases j <;> simp_all [endpointU, pauliWord_mul, letterPhase, letterProduct]

/-- Equation (4) for the signed two-mode endpoint, in homogeneous form on PiL2. -/
theorem pauli_frame_overlap_le_two (u v : EuclideanSpace ℂ Mode) :
    ‖⟪u, v⟫_ℂ‖ ^ 2 + ∑ j : Fin 4, ‖⟪u, (endpointU j).toEuclideanLin v⟫_ℂ‖ ^ 2 ≤
      2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  apply WuEndpointPauliFrame.overlap_le (fun j => (endpointU j).toEuclideanLin)
  · exact fun j => Matrix.isSymmetric_toEuclideanLin_iff.mpr (endpointU_hermitian j)
  · intro j x
    change ((Matrix.toLpLin 2 2 (endpointU j)).comp
      (Matrix.toLpLin 2 2 (endpointU j))) x = x
    rw [← Matrix.toLpLin_mul, endpointU_sq, Matrix.toLpLin_one, LinearMap.id_apply]
  · intro i j hij x
    change ((Matrix.toLpLin 2 2 (endpointU i)).comp (Matrix.toLpLin 2 2 (endpointU j))) x =
      -((Matrix.toLpLin 2 2 (endpointU j)).comp (Matrix.toLpLin 2 2 (endpointU i))) x
    rw [← Matrix.toLpLin_mul, ← Matrix.toLpLin_mul, endpointU_anticommute i j hij,
      map_neg, LinearMap.neg_apply]

/-- Conjugation by the j-th Pauli word flips precisely the j-th Clifford generator. -/
theorem endpointU_conj_gamma (j k : Fin 4) :
    endpointU j * endpointGamma k * (endpointU j)ᴴ =
      if j = k then -endpointGamma k else endpointGamma k := by
  rw [(endpointU_hermitian j).eq]
  fin_cases j <;> fin_cases k <;>
    simp [endpointU, endpointGamma, pauliWord_mul, letterPhase, letterProduct,
      smul_smul, Complex.I_mul_I]

/-- The ordered product of all four conjugating words. -/
def endpointVolume : TwoMode :=
  endpointU 0 * endpointU 1 * endpointU 2 * endpointU 3

/-- The ordered triples, indexed by the generator omitted from the product. -/
def endpointTriple : Fin 4 → TwoMode :=
  ![endpointU 1 * endpointU 2 * endpointU 3, endpointU 0 * endpointU 2 * endpointU 3,
    endpointU 0 * endpointU 1 * endpointU 3, endpointU 0 * endpointU 1 * endpointU 2]

private theorem endpointVolume_eq : endpointVolume = -pauliWord .Z .Z := by
  simp [endpointVolume, endpointU, pauliWord_mul, letterPhase, letterProduct,
    smul_smul, Complex.I_mul_I]

private theorem endpointVolume_mul_U (j : Fin 4) :
    endpointVolume * endpointU j =
      if j = 0 ∨ j = 2 then -endpointTriple j else endpointTriple j := by
  rw [endpointVolume_eq]
  fin_cases j <;> simp [endpointU, endpointTriple, pauliWord_mul, letterPhase,
    letterProduct, smul_smul, Complex.I_mul_I]

/-- The squared-overlap bound for the four ordered triples and the full product. -/
theorem pauli_tail_overlap_le_two (u v : EuclideanSpace ℂ Mode) :
    ‖⟪u, endpointVolume.toEuclideanLin v⟫_ℂ‖ ^ 2 +
      ∑ j : Fin 4, ‖⟪u, (endpointTriple j).toEuclideanLin v⟫_ℂ‖ ^ 2 ≤
    2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  let V := endpointVolume.toEuclideanLin
  have hV : V.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    simp [Matrix.IsHermitian, endpointVolume_eq, pauliWord, Matrix.conjTranspose_kronecker,
      pauli_hermitian]
  have hsq : endpointVolume * endpointVolume = 1 := by
    simp [endpointVolume_eq, pauliWord_mul, letterPhase, letterProduct, pauliWord_one]
  have hVu : ‖V u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), hV u (V u)]
    change RCLike.re ⟪u, (Matrix.toLpLin 2 2 endpointVolume ∘ₗ
      Matrix.toLpLin 2 2 endpointVolume) u⟫_ℂ = _
    rw [← Matrix.toLpLin_mul_same, hsq, Matrix.toLpLin_one, LinearMap.id_apply,
      ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  have hterm (j : Fin 4) : ‖⟪V u, (endpointU j).toEuclideanLin v⟫_ℂ‖ ^ 2 =
      ‖⟪u, (endpointTriple j).toEuclideanLin v⟫_ℂ‖ ^ 2 := by
    rw [hV]
    change ‖⟪u, (Matrix.toLpLin 2 2 endpointVolume ∘ₗ
      Matrix.toLpLin 2 2 (endpointU j)) v⟫_ℂ‖ ^ 2 = _
    rw [← Matrix.toLpLin_mul_same, endpointVolume_mul_U]
    split_ifs <;> simp
  simpa only [hV u v, hterm, hVu] using pauli_frame_overlap_le_two (V u) v

#print axioms endpointU_conj_gamma
#print axioms pauli_frame_overlap_le_two
#print axioms pauli_tail_overlap_le_two

end WuRankOneEndpointFloor
