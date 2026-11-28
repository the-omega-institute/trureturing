/- GID: D5/S3/Quantum/Foundation/FiniteHermitianSign
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FiniteHermitianSign
   mirror-E: none(waiver:finite-dimensional-algebraic-proof)
   anchors: []
   utility: none
   digest: The finite Hermitian sign, its spectral subspaces and its trace pairing. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Mathlib.Basic.Real.Sign

/-! # The finite Hermitian sign -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Foundation.FiniteHermitianSign

open Matrix
open scoped ComplexOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)

variable {n : ℕ}

/-- The canonical Hermitian sign given by spectral calculus, with sign zero at zero. -/
def hermitianSign {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    Matrix (Fin n) (Fin n) ℂ :=
  hA.cfc Real.sign

private theorem spectral_calc_mulVec {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (i : Fin n) :
    hA.cfc f *ᵥ (hA.eigenvectorBasis i).ofLp =
      (f (hA.eigenvalues i) : ℂ) • (hA.eigenvectorBasis i).ofLp := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA.star_eigenvectorUnitary_mulVec,
    Matrix.diagonal_mulVec_single, mul_one]
  have h : (RCLike.ofReal ∘ f ∘ hA.eigenvalues) i =
      (f (hA.eigenvalues i) : ℂ) • (1 : ℂ) := by
    change (f (hA.eigenvalues i) : ℂ) = _
    simp
  rw [h]
  rw [Pi.single_smul', Matrix.mulVec_smul, hA.eigenvectorUnitary_mulVec]

private def spectralSubspace {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (s : Set (Fin n)) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ ((fun i => (hA.eigenvectorBasis i).ofLp) '' s)

private theorem spectral_calc_eq_smul_iff {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (c : ℝ) (x : Fin n → ℂ) :
    hA.cfc f *ᵥ x = (c : ℂ) • x ↔
      x ∈ spectralSubspace hA {i | f (hA.eigenvalues i) = c} := by
  classical
  let b := hA.eigenvectorBasis.toBasis.map (WithLp.linearEquiv 2 ℂ (Fin n → ℂ))
  have hb (i : Fin n) : b i = (hA.eigenvectorBasis i).ofLp := rfl
  have hcoord (i : Fin n) :
      b.repr (hA.cfc f *ᵥ x) i = (f (hA.eigenvalues i) : ℂ) * b.repr x i := by
    have hb' (j : Fin n) :
        hA.cfc f *ᵥ b j = (f (hA.eigenvalues j) : ℂ) • b j := by
      rw [hb, spectral_calc_mulVec]
    conv_lhs => rw [← b.sum_repr x]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hb', smul_smul]
    change (Finsupp.lapply i ∘ₗ b.repr.toLinearMap) _ = _
    simp [map_sum, Module.Basis.repr_self, Finsupp.single_apply, mul_comm]
  change _ ↔ x ∈ Submodule.span ℂ (b '' _)
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h i hi
    have he := congrArg (fun z => b.repr z i) h
    rw [hcoord, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at he
    exact_mod_cast (mul_right_cancel₀ (Finsupp.mem_support_iff.mp hi) he)
  · intro h
    apply b.repr.injective
    ext i
    rw [hcoord, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i ∈ (b.repr x).support
    · have he : f (hA.eigenvalues i) = c := h hi
      rw [he]
    · simp [Finsupp.notMem_support_iff.mp hi]

/-- The strict positive spectral subspace of a Hermitian matrix. -/
def positiveSubspace {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    Submodule ℂ (Fin n → ℂ) :=
  spectralSubspace hA {i | 0 < hA.eigenvalues i}

/-- The strict negative spectral subspace of a Hermitian matrix. -/
def negativeSubspace {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    Submodule ℂ (Fin n → ℂ) :=
  spectralSubspace hA {i | hA.eigenvalues i < 0}

private theorem real_sign_facts (a : ℝ) :
    -1 ≤ Real.sign a ∧ Real.sign a ≤ 1 ∧
    (Real.sign a = 1 ↔ 0 < a) ∧ (Real.sign a = -1 ↔ a < 0) ∧
    Real.sign a * a = |a| := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · norm_num [Real.sign_of_neg ha, ha, not_lt_of_ge ha.le, abs_of_neg ha]
  · norm_num
  · norm_num [Real.sign_of_pos ha, ha, not_lt_of_ge ha.le, abs_of_pos ha]

/-- The sign has the same kernel and has extremal eigenspaces given by the
strictly positive and strictly negative spectral subspaces. -/
theorem hermitianSign_eigenspaces {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (x : Fin n → ℂ) :
    (hermitianSign hA *ᵥ x = 0 ↔ A *ᵥ x = 0) ∧
    (hermitianSign hA *ᵥ x = x ↔ x ∈ positiveSubspace hA) ∧
    (hermitianSign hA *ᵥ x = -x ↔ x ∈ negativeSubspace hA) := by
  have hid : hA.cfc id = A := hA.spectral_theorem.symm
  refine ⟨?_, ?_, ?_⟩
  · have h := spectral_calc_eq_smul_iff hA Real.sign 0 x
    simp only [Real.sign_eq_zero_iff, Complex.ofReal_zero, zero_smul] at h
    rw [hermitianSign, h]
    simpa [hid] using (spectral_calc_eq_smul_iff hA id 0 x).symm
  · simpa [hermitianSign, positiveSubspace, (real_sign_facts _).2.2.1] using
      spectral_calc_eq_smul_iff hA Real.sign 1 x
  · simpa [hermitianSign, negativeSubspace, (real_sign_facts _).2.2.2.1] using
      spectral_calc_eq_smul_iff hA Real.sign (-1) x

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- The Hermitian sign is a contraction and its trace pairing attains the trace norm. -/
theorem hermitianSign_spec {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (hermitianSign hA).IsHermitian ∧
    (1 - hermitianSign hA).PosSemidef ∧ (1 + hermitianSign hA).PosSemidef ∧
    (hermitianSign hA * A).trace.re = traceNorm A := by
  let U := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) hA.eigenvectorUnitary
  let d (f : ℝ → ℝ) := diagonal (fun i => (f (hA.eigenvalues i) : ℂ))
  have hs : hermitianSign hA = U (d Real.sign) := rfl
  have hA' : A = U (d id) := hA.spectral_theorem
  have hminus : (1 - d Real.sign).PosSemidef := by
    unfold d
    rw [← diagonal_one, diagonal_sub, posSemidef_diagonal_iff]
    intro i
    exact Complex.nonneg_iff.mpr ⟨by
      change 0 ≤ (1 : ℂ).re - (Real.sign (hA.eigenvalues i) : ℂ).re
      simpa using sub_nonneg.mpr (real_sign_facts (hA.eigenvalues i)).2.1, by simp⟩
  have hplus : (1 + d Real.sign).PosSemidef := by
    unfold d
    rw [← diagonal_one, diagonal_add, posSemidef_diagonal_iff]
    intro i
    exact Complex.nonneg_iff.mpr ⟨by
      change 0 ≤ (1 : ℂ).re + (Real.sign (hA.eigenvalues i) : ℂ).re
      simp only [Complex.one_re, Complex.ofReal_re]
      linarith [(real_sign_facts (hA.eigenvalues i)).1], by simp⟩
  have hconj (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) : (U B).PosSemidef := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      using hB.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  have hm : (1 - hermitianSign hA).PosSemidef := by
    rw [hs, ← map_one U, ← map_sub U]
    exact hconj _ hminus
  have hp : (1 + hermitianSign hA).PosSemidef := by
    rw [hs, ← map_one U, ← map_add U]
    exact hconj _ hplus
  refine ⟨?_, hm, hp, ?_⟩
  · exact (isHermitian_one.sub hm.isHermitian : (1 - (1 - hermitianSign hA)).IsHermitian)
      |> fun h => by simpa using h
  · change (hermitianSign hA * A).trace.re = (CFC.abs A).trace.re
    rw [CFC.abs_eq_cfc_norm A hA.isSelfAdjoint, hA.cfc_eq]
    have hprod : hermitianSign hA * A = U (d fun x => ‖x‖) := calc
      hermitianSign hA * A = U (d Real.sign) * U (d id) := congrArg₂ (· * ·) hs hA'
      _ = U (d Real.sign * d id) := (map_mul U _ _).symm
      _ = U (d fun x => ‖x‖) := by
        congr 1
        simp only [d, diagonal_mul_diagonal, id_eq, ← Complex.ofReal_mul, Real.norm_eq_abs,
          (real_sign_facts _).2.2.2.2]
    rw [hprod]
    rfl

end D5.S3.Quantum.Foundation.FiniteHermitianSign
