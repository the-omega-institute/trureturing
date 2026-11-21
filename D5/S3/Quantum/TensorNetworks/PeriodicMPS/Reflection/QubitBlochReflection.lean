/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/QubitBlochReflection
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/QubitBlochReflection
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.Measurement.Bloch.QubitBloch]
   utility: none
   digest: A reflection selected by a degenerate Bloch Krylov matrix. -/
import D5.S3.Quantum.Measurement.Bloch.QubitBloch
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.QubitBlochReflection

open Matrix
open scoped Matrix ComplexConjugate
open WithLp
open Measurement.FourQubitParentConstruction (B B_formula_core)

noncomputable section

abbrev BlochVector := Fin 3 → ℝ
abbrev BlochMatrix := Matrix (Fin 3) (Fin 3) ℝ
abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

private theorem cube_eq_lower_powers (C : BlochMatrix) :
    C ^ 3 = -C.charpoly.coeff 0 • (1 : BlochMatrix) -
      C.charpoly.coeff 1 • C - C.charpoly.coeff 2 • C ^ 2 := by
  have h := C.aeval_self_charpoly
  rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim] at h
  have h₃ : C.charpoly.coeff 3 = 1 := by
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using
      C.charpoly_monic.coeff_natDegree
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    h₃, pow_zero, pow_one, Algebra.smul_def, map_one, one_mul] at h
  simp only [← Algebra.smul_def] at h
  calc
    C ^ 3 = -(C.charpoly.coeff 0 • (1 : BlochMatrix) + C.charpoly.coeff 1 • C +
        C.charpoly.coeff 2 • C ^ 2) := eq_neg_of_add_eq_zero_left (by rwa [add_comm])
    _ = _ := by simp only [neg_smul]; abel

/-- The columns are ordered as in the literal two-site chirality readout. -/
def krylovMatrix (r : BlochVector) (C : BlochMatrix) : BlochMatrix :=
  Matrix.of fun i => ![r i, (C *ᵥ r) i, (C ^ 2 *ᵥ r) i]

set_option maxHeartbeats 1000000 in
/-- A singular Krylov matrix supplies a unit eigenvector normal to the Krylov span.
Cayley–Hamilton makes the span invariant and symmetry passes invariance to its
orthogonal complement. -/
theorem exists_unit_eigenvector_of_krylov_det_zero (r : BlochVector) (C : BlochMatrix)
    (hC : Cᵀ = C) (hdet : (krylovMatrix r C).det = 0) :
    ∃ v : BlochVector, v ⬝ᵥ v = 1 ∧ v ⬝ᵥ r = 0 ∧ ∃ μ : ℝ, C *ᵥ v = μ • v := by
  let K := krylovMatrix r C
  let W := LinearMap.range K.toEuclideanLin
  let T := C.toEuclideanLin
  have hcol (i : Fin 3) : toLp 2 (K.col i) ∈ W := by
    refine ⟨toLp 2 (Pi.single i 1), ?_⟩
    change toLp 2 (K *ᵥ Pi.single i 1) = _
    congr 1
    ext j
    simp [mulVec, dotProduct, Matrix.col, mul_ite, Pi.single_apply]
  have hr : toLp 2 r ∈ W := hcol 0
  have hr₁ : toLp 2 (C *ᵥ r) ∈ W := hcol 1
  have hr₂ : toLp 2 (C ^ 2 *ᵥ r) ∈ W := hcol 2
  have hr₃ : toLp 2 (C ^ 3 *ᵥ r) ∈ W := by
    rw [cube_eq_lower_powers, sub_mulVec, sub_mulVec, smul_mulVec, one_mulVec, smul_mulVec,
      smul_mulVec]
    exact W.sub_mem (W.sub_mem (W.smul_mem _ hr) (W.smul_mem _ hr₁)) (W.smul_mem _ hr₂)
  have hspan : W = Submodule.span ℝ (Set.range fun i : Fin 3 => toLp 2 (K.col i)) := by
    let e := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
    have hW : W = Submodule.map e.symm.toLinearMap K.mulVecLin.range := by
      ext x
      change (∃ y, K.toEuclideanLin y = x) ↔ _
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨K *ᵥ y.ofLp, ⟨y.ofLp, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨toLp 2 y, rfl⟩
    rw [hW, Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    rfl
  have hInv : W ∈ Module.End.invtSubmodule T := by
    change ∀ x ∈ W, T x ∈ W
    intro x hx
    rw [hspan] at hx
    apply Submodule.span_induction (p := fun x _ => T x ∈ W) _ _ _ _ hx
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hr₁
      · change toLp 2 (C *ᵥ (C *ᵥ r)) ∈ W
        rwa [mulVec_mulVec, ← pow_two]
      · change toLp 2 (C *ᵥ (C ^ 2 *ᵥ r)) ∈ W
        rwa [mulVec_mulVec, ← pow_succ']
    · rw [map_zero]; exact W.zero_mem
    · intro x y _ _ hx hy
      rw [map_add]; exact W.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]; exact W.smul_mem _ hx
  have hW : W ≠ ⊤ := by
    intro he
    have hs : Function.Surjective K.toEuclideanLin := LinearMap.range_eq_top.mp he
    have hsm : Function.Surjective (K *ᵥ ·) := by
      intro y
      obtain ⟨x, hx⟩ := hs (toLp 2 y)
      exact ⟨x.ofLp, congrArg ofLp hx⟩
    have hu := (Matrix.isUnit_iff_isUnit_det K).mp (mulVec_surjective_iff_isUnit.mp hsm)
    exact hu.ne_zero hdet
  have hsym : T.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr
    (show C.IsHermitian by
      change Cᴴ = C
      convert hC using 1
      ext i j
      simp [Matrix.conjTranspose_apply])
  have hperp := hsym.orthogonalComplement_mem_invtSubmodule hInv
  have hn : 0 < Module.finrank ℝ Wᗮ :=
    Nat.pos_of_ne_zero (fun h => hW (Submodule.orthogonal_eq_bot_iff.mp
      (Submodule.finrank_eq_zero.mp h)))
  let i : Fin (Module.finrank ℝ Wᗮ) := ⟨0, hn⟩
  have hs := hsym.restrict_invariant hperp
  let v := hs.eigenvectorBasis rfl i
  have he := hs.hasEigenvector_eigenvectorBasis rfl i
  have hnorm : ‖v‖ = 1 := (hs.eigenvectorBasis rfl).norm_eq_one i
  have hinner : inner ℝ (v : EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3)) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    change ‖v‖ ^ 2 = 1
    rw [hnorm, one_pow]
  have horth := v.property (toLp 2 r) hr
  refine ⟨(v : EuclideanSpace ℝ (Fin 3)).ofLp, ?_, ?_, hs.eigenvalues rfl i, ?_⟩
  · simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hinner
  · rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at horth
    exact horth
  · exact congrArg (fun w : Wᗮ => (w : EuclideanSpace ℝ (Fin 3)).ofLp) he.apply_eq_smul

/-- The plane reflection with normal `v` when `v` has Euclidean norm one. -/
def reflection (v : BlochVector) : BlochMatrix := 1 - (2 : ℝ) • vecMulVec v v

theorem reflection_transpose (v : BlochVector) : (reflection v)ᵀ = reflection v := by
  simp [reflection, transpose_vecMulVec]

theorem reflection_apply (v x : BlochVector) :
    reflection v *ᵥ x = x - (2 * (v ⬝ᵥ x)) • v := by
  rw [reflection, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec]
  ext i
  change x i - (2 : ℝ) * (v i * (v ⬝ᵥ x)) = x i - (2 * (v ⬝ᵥ x)) * v i
  ring

theorem reflection_fixes_vector (v r : BlochVector) (h : v ⬝ᵥ r = 0) :
    reflection v *ᵥ r = r := by simp [reflection_apply, h]

theorem reflection_square (v : BlochVector) (hv : v ⬝ᵥ v = 1) :
    reflection v * reflection v = 1 := by
  have hp : vecMulVec v v * vecMulVec v v = vecMulVec v v := by
    rw [vecMulVec_mul_vecMulVec, hv, one_smul]
  simp only [reflection, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hp, smul_smul]
  module

theorem reflection_fixes_correlation (v : BlochVector) (C : BlochMatrix)
    (hv : v ⬝ᵥ v = 1) (hC : Cᵀ = C) {μ : ℝ} (he : C *ᵥ v = μ • v) :
    reflection v * C * (reflection v)ᵀ = C := by
  have hleft : v ᵥ* C = μ • v := by rw [← mulVec_transpose, hC, he]
  have hcomm : reflection v * C = C * reflection v := by
    simp only [reflection, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul,
      Matrix.mul_smul, vecMulVec_mul, mul_vecMulVec, hleft, he]
    rw [vecMulVec_smul, smul_vecMulVec]
  rw [reflection_transpose, hcomm, Matrix.mul_assoc, reflection_square v hv, Matrix.mul_one]

/-- Entrywise complex conjugation in the computational basis. -/
def conjEntries {ι κ : Type*} (M : Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  M.map (starRingEnd ℂ)

@[simp] theorem conjEntries_apply {ι κ : Type*} (M : Matrix ι κ ℂ) (i : ι) (j : κ) :
    conjEntries M i j = conj (M i j) := rfl

theorem conjEntries_mul {ι κ η : Type*} [Fintype κ]
    (M : Matrix ι κ ℂ) (N : Matrix κ η ℂ) :
    conjEntries (M * N) = conjEntries M * conjEntries N :=
  Matrix.map_mul (f := starRingEnd ℂ)

@[simp] theorem conjEntries_conjEntries {ι κ : Type*} (M : Matrix ι κ ℂ) :
    conjEntries (conjEntries M) = M := by ext; simp

/-- Matrix part of the qubit antiunitary. This is `-B(v) · iσ_y`, with a
global phase chosen to give the displayed symmetric matrix. -/
def reflectionUnitary (v : BlochVector) : QubitMatrix :=
  !![(v 0 : ℂ) - Complex.I * (v 1 : ℂ), -(v 2 : ℂ);
    -(v 2 : ℂ), -(v 0 : ℂ) - Complex.I * (v 1 : ℂ)]

theorem reflectionUnitary_transpose (v : BlochVector) :
    (reflectionUnitary v)ᵀ = reflectionUnitary v := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem reflectionUnitary_adjoint (v : BlochVector) :
    (reflectionUnitary v)ᴴ = conjEntries (reflectionUnitary v) := by
  change conjEntries (reflectionUnitary v)ᵀ = _
  rw [reflectionUnitary_transpose]

theorem reflectionUnitary_involution (v : BlochVector) (hv : v ⬝ᵥ v = 1) :
    reflectionUnitary v * conjEntries (reflectionUnitary v) = 1 := by
  rw [dotProduct, Fin.sum_univ_three] at hv
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [reflectionUnitary, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;>
    nlinarith only [hv]

theorem reflectionUnitary_mem (v : BlochVector) (hv : v ⬝ᵥ v = 1) :
    reflectionUnitary v ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, reflectionUnitary_adjoint]
  exact reflectionUnitary_involution v hv

private theorem conjugate_bloch_formula (v x : BlochVector) :
    reflectionUnitary v * conjEntries (B (toLp 2 x)) * (reflectionUnitary v)ᴴ =
      B (toLp 2 ((v ⬝ᵥ v) • x - (2 * (v ⬝ᵥ x)) • v)) := by
  rw [reflectionUnitary_adjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [reflectionUnitary, B_formula_core, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      dotProduct, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;> ring

/-- The antiunitary induces the specified plane reflection on the Pauli coordinates. -/
theorem conjugate_bloch (v x : BlochVector) (hv : v ⬝ᵥ v = 1) :
    reflectionUnitary v * conjEntries (B (toLp 2 x)) * (reflectionUnitary v)ᴴ =
      B (toLp 2 (reflection v *ᵥ x)) := by
  rw [conjugate_bloch_formula, reflection_apply, hv, one_smul]

end
end D5.S3.Quantum.TensorNetworks.QubitBlochReflection
