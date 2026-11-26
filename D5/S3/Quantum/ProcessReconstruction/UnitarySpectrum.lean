/- GID: D5/S3/Quantum/ProcessReconstruction/UnitarySpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/UnitarySpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative unitary spectral chords and finite reference expectations. -/

import D5.S3.Quantum.ProcessReconstruction.SwapReconstruction
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-! Relative unitary spectral chords and finite reference expectations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder CStarAlgebra
  Matrix.Norms.L2Operator InnerProductSpace ComplexStarModule

namespace UnitaryReconstruction

variable {a r : Type*} [Fintype a] [DecidableEq a] [Fintype r] [DecidableEq r]

local notation "ℓ²" => EuclideanSpace ℂ
local notation "L" => Matrix.toEuclideanCLM (𝕜 := ℂ)

theorem kronUnitary (U : unitaryGroup a ℂ) (V : unitaryGroup r ℂ) :
    U.val ⊗ₖ V.val ∈ unitaryGroup (a × r) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  have hu : U.val * U.valᴴ = 1 := Unitary.mul_star_self_of_mem U.prop
  have hv : V.val * V.valᴴ = 1 := Unitary.mul_star_self_of_mem V.prop
  change (U.val ⊗ₖ V.val) * (U.val ⊗ₖ V.val)ᴴ = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hu, hv,
    Matrix.one_kronecker_one]

def relativeUnitary (U V : unitaryGroup a ℂ) : unitaryGroup a ℂ := star V * U

theorem relative_kron_norm (U V : unitaryGroup a ℂ) :
    opNorm ((relativeUnitary U V).valᴴ ⊗ₖ (relativeUnitary U V).val - 1) =
      opNorm (U.valᴴ ⊗ₖ U.val - V.valᴴ ⊗ₖ V.val) := by
  let B : unitaryGroup (a × a) ℂ := ⟨(1 : Matrix a a ℂ) ⊗ₖ V.valᴴ, kronUnitary 1 (star V)⟩
  let C : unitaryGroup (a × a) ℂ := ⟨V.val ⊗ₖ (1 : Matrix a a ℂ), kronUnitary V 1⟩
  have h : B.val * (U.valᴴ ⊗ₖ U.val - V.valᴴ ⊗ₖ V.val) * C.val =
      (relativeUnitary U V).valᴴ ⊗ₖ (relativeUnitary U V).val - 1 := by
    change ((1 : Matrix a a ℂ) ⊗ₖ V.valᴴ) *
      (U.valᴴ ⊗ₖ U.val - V.valᴴ ⊗ₖ V.val) * (V.val ⊗ₖ (1 : Matrix a a ℂ)) =
      (V.valᴴ * U.val)ᴴ ⊗ₖ (V.valᴴ * U.val) - 1
    have hv : V.valᴴ * V.val = 1 := Unitary.star_mul_self_of_mem V.prop
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, hv, Matrix.one_kronecker_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [← h, opNorm_unitary_right, opNorm_unitary_left]

theorem spectrum_eigenvector (W : Matrix a a ℂ) (z : ℂ) (hz : z ∈ spectrum ℂ W) :
    ∃ v : a → ℂ, v ≠ 0 ∧ W *ᵥ v = z • v := by
  have h : Module.End.HasEigenvalue W.toLin' z :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr (by simpa using hz)
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  exact ⟨v, hv.2, Module.End.mem_eigenspace_iff.mp hv.1⟩

theorem spectrum_chord_le (W : unitaryGroup a ℂ) (p q : ℂ)
    (hp : p ∈ spectrum ℂ W.val) (hq : q ∈ spectrum ℂ W.val) :
    ‖p - q‖ ≤ opNorm (W.valᴴ ⊗ₖ W.val - 1) := by
  obtain ⟨x, hx, hpx⟩ := spectrum_eigenvector W.val p hp
  obtain ⟨y, hy, hqy⟩ := spectrum_eigenvector W.val q hq
  have hpn : ‖p‖ = 1 := spectrum.norm_eq_one_of_unitary W.prop hp
  have hpc : star p * p = 1 := by
    rw [mul_comm, show p * star p = (‖p‖ : ℂ) ^ 2 from Complex.mul_conj' p, hpn]
    norm_num
  have hw : W.valᴴ * W.val = 1 := Unitary.star_mul_self_of_mem W.prop
  have hpx' : W.valᴴ *ᵥ x = star p • x := by
    have h := congrArg (W.valᴴ *ᵥ ·) hpx
    rw [Matrix.mulVec_mulVec, hw, Matrix.one_mulVec, Matrix.mulVec_smul] at h
    calc
      _ = (star p * p) • (W.valᴴ *ᵥ x) := by rw [hpc, one_smul]
      _ = star p • x := by rw [← smul_smul, ← h]
  let v : a × a → ℂ := fun ij => x ij.1 * y ij.2
  have hv : v ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! h
      exact hx (funext h)
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra! h
      exact hy (funext h)
    intro h
    exact mul_ne_zero hi hj (congrFun h (i,j))
  let A := W.valᴴ ⊗ₖ W.val - 1
  have hkv (i j : a) :
      ((W.valᴴ ⊗ₖ W.val) *ᵥ v) (i,j) = (W.valᴴ *ᵥ x) i * (W.val *ᵥ y) j := by
    simp only [v, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have he : A *ᵥ v = (star p * q - 1) • v := by
    ext ⟨i,j⟩
    simp only [A, Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec, hkv, hpx', hqy,
      Pi.smul_apply, smul_eq_mul, v]
    ring
  let u : ℓ² (a × a) := WithLp.toLp 2 v
  have hu : 0 < ‖u‖ := by simpa [u, norm_pos_iff] using hv
  have h := A.l2_opNorm_mulVec u
  change ‖L A u‖ ≤ ‖A‖ * ‖u‖ at h
  rw [Matrix.toEuclideanCLM_toLp, he, WithLp.toLp_smul, norm_smul] at h
  have hn : ‖star p * q - 1‖ = ‖p - q‖ := by
    rw [← hpc, ← mul_sub, norm_mul, norm_star, hpn, one_mul, norm_sub_rev]
  rw [hn] at h
  exact le_of_mul_le_mul_right h hu

theorem reference_spectrum_subset (W : unitaryGroup a ℂ) :
    spectrum ℂ (referenceUnitary r W).val ⊆ spectrum ℂ W.val := by
  intro z hz
  obtain ⟨v, hv, hzv⟩ := spectrum_eigenvector _ z hz
  have hSlice (i : r) (j : a) :
      ((referenceUnitary r W).val *ᵥ v) (i,j) = (W.val *ᵥ fun k => v (i,k)) j := by
    simp [referenceUnitary, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply]
  obtain ⟨i, hi⟩ : ∃ i : r, (fun j : a => v (i,j)) ≠ 0 := by
    by_contra! h
    apply hv
    ext ⟨i,j⟩
    exact congrFun (h i) j
  have he : W.val *ᵥ (fun j => v (i,j)) = z • (fun j => v (i,j)) := by
    funext j
    rw [← hSlice]
    exact congrFun hzv (i,j)
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr he, hi⟩

set_option maxHeartbeats 1200000 in
-- Elaborating the positive real part via functional calculus needs a larger budget.
set_option backward.isDefEq.respectTransparency false in
theorem re_inner_ge_of_spectrum [Nonempty a] (W : unitaryGroup a ℂ) (c : ℂ)
    (t : ℝ) (ht : ∀ z ∈ spectrum ℂ W.val, t ≤ (c * z).re)
    (v : ℓ² a) (hv : ‖v‖ = 1) : t ≤ (c * ⟪v, L W.val v⟫_ℂ).re := by
  let Z := c • W.val
  have hz : IsStarNormal Z := (isStarNormal_of_mem_unitary W.prop).smul c
  have hs : ∀ x ∈ spectrum ℝ (ℜ Z : Matrix a a ℂ), t ≤ x := by
    rw [spectrum_realPart' Z hz]
    rintro _ ⟨z, hz', rfl⟩
    rw [show Z = c • W.val from rfl, spectrum.smul_eq_smul c W.val (spectrum.nonempty W.val)] at hz'
    rcases hz' with ⟨w, hw, rfl⟩
    exact ht w hw
  let H : Matrix a a ℂ := (ℜ Z : Matrix a a ℂ) - algebraMap ℝ (Matrix a a ℂ) t
  have hH : H.PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    have hsa : IsSelfAdjoint H :=
      (ℜ Z).prop.sub ((show IsSelfAdjoint t from rfl).algebraMap (Matrix a a ℂ))
    apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) H hsa).mpr
    intro x hx
    change x ∈ spectrum ℝ ((ℜ Z : Matrix a a ℂ) - algebraMap ℝ _ t) at hx
    rw [← spectrum.sub_singleton_eq] at hx
    obtain ⟨y, hy, z, hz, hyz⟩ := hx
    have hz' : z = t := hz
    subst z
    rw [← hyz]
    exact sub_nonneg.mpr (hs y hy)
  have hn := hH.re_dotProduct_nonneg (⇑v)
  rw [dotProduct_comm, ← Matrix.ofLp_toEuclideanCLM,
    ← EuclideanSpace.inner_eq_star_dotProduct] at hn
  change 0 ≤ (⟪v, L H v⟫_ℂ).re at hn
  have hconj (X : Matrix a a ℂ) :
      L Xᴴ = (L X).adjoint := by
    exact map_star L X
  have hreal : (⟪v, L H v⟫_ℂ).re = (c * ⟪v, L W.val v⟫_ℂ).re - t := by
    have hinner : ⟪v, L Zᴴ v⟫_ℂ = star ⟪v, L Z v⟫_ℂ := by
      rw [hconj, ContinuousLinearMap.adjoint_inner_right]
      exact (inner_conj_symm _ _).symm
    have hH' : H = (2 : ℂ)⁻¹ • (Z + Zᴴ) - (t : ℂ) • 1 := by
      change (ℜ Z : Matrix a a ℂ) - algebraMap ℝ (Matrix a a ℂ) t = _
      rw [realPart_apply_coe, Matrix.star_eq_conjTranspose, Algebra.algebraMap_eq_smul_one]
      rw [← IsScalarTower.algebraMap_smul ℂ ((2 : ℝ)⁻¹),
        ← IsScalarTower.algebraMap_smul ℂ t]
      push_cast
      rfl
    have hZ : ⟪v, L Z v⟫_ℂ = c * ⟪v, L W.val v⟫_ℂ := by
      simp only [Z, map_smul, _root_.smul_apply, inner_smul_right]
    rw [hH']
    simp only [map_sub, map_smul, map_add, map_one, _root_.sub_apply, _root_.smul_apply,
      _root_.add_apply, one_apply_eq_self, inner_sub_right, inner_add_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hv, hinner, hZ]
    let w := c * ⟪v, L W.val v⟫_ℂ
    have hw : w + star w = (2 : ℂ) * (w.re : ℂ) := by
      apply Complex.ext <;> simp [two_mul]
    change ((2 : ℂ)⁻¹ * (w + star w) - (t : ℂ) * ((1 : ℂ) ^ 2)).re = w.re - t
    rw [hw, ← mul_assoc]
    norm_num
  rw [hreal] at hn
  linarith

end UnitaryReconstruction
