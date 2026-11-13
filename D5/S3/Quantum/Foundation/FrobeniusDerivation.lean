/- GID: D5/S3/Quantum/Foundation/FrobeniusDerivation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FrobeniusDerivation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derivations of finite positive unital Frobenius comparisons are skew adjoint. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Derivations preserve the positive Frobenius pairing without associativity.
The trace pairing first forces a derivation to annihilate every element whose
left multiplication commutes with all left multiplications. -/

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace BigOperators

namespace D5.S3.Quantum.Foundation.FrobeniusDerivation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

private theorem derivation_kills_central_multiplier
    (S : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : V)
    (comm : ∀ x y, S x y = S y x)
    (unit : ∀ x, S e x = x)
    (frob : ∀ x y z, ⟪S x y, z⟫_ℝ = ⟪y, S x z⟫_ℝ)
    (d : V →ₗ[ℝ] V)
    (der : ∀ x y, d (S x y) = S (d x) y + S x (d y))
    (c : V) (central : ∀ x, Commute (S c) (S x)) : d c = 0 := by
  classical
  let C := S (d c)
  have hC : C = d * S c - S c * d := by
    ext x
    simp only [C, LinearMap.sub_apply, Module.End.mul_apply, der]
    abel
  have htrace : LinearMap.trace ℝ V (C * C) = 0 := by
    calc
      _ = LinearMap.trace ℝ V (⁅d, S c⁆ * C) := by rw [Ring.lie_def, ← hC]
      _ = LinearMap.trace ℝ V (d * ⁅S c, C⁆) := LinearMap.trace_lie_mul_eq d (S c) C
      _ = 0 := by simp [Ring.lie_def, (central (d c)).eq, C]
  let b := stdOrthonormalBasis ℝ V
  have symC : C.IsSymmetric := frob (d c)
  have matrix_adjoint : (C.toMatrix b.toBasis b.toBasis).conjTranspose =
      C.toMatrix b.toBasis b.toBasis := by
    rw [← LinearMap.toMatrix_adjoint b b, symC.adjoint_eq]
  have hzero : C = 0 := by
    apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
    rw [map_zero]
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    rw [matrix_adjoint, ← LinearMap.toMatrix_mul,
      ← LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
    exact htrace
  have he := congrArg (fun T : V →ₗ[ℝ] V => T e) hzero
  simpa only [C, comm (d c) e, unit, LinearMap.zero_apply] using he

/-- Every derivation of the original positive Frobenius multiplication is skew-adjoint.
The unit need not be normalized, and the multiplication need not be associative. -/
theorem derivation_skew_adjoint
    (S : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : V)
    (comm : ∀ x y, S x y = S y x)
    (unit : ∀ x, S e x = x)
    (frob : ∀ x y z, ⟪S x y, z⟫_ℝ = ⟪y, S x z⟫_ℝ)
    (d : V →ₗ[ℝ] V)
    (der : ∀ x y, d (S x y) = S (d x) y + S x (d y))
    (x y : V) : ⟪d x, y⟫_ℝ = -⟪x, d y⟫_ℝ := by
  have de : d e = 0 := by
    have h := der e e
    rw [unit, unit, comm (d e) e, unit] at h
    exact add_eq_left.mp h.symm
  have dadj (a z : V) :
      d.adjoint (S a z) = S a (d.adjoint z) - S (d a) z := by
    apply ext_inner_right ℝ
    intro w
    simp only [LinearMap.adjoint_inner_left, inner_sub_left, frob]
    rw [der, inner_add_right]
    ring
  let H := d + d.adjoint
  have hH (a z : V) : H (S a z) = S a (H z) := by
    simp only [H, LinearMap.add_apply, der, dadj, map_add]
    abel
  let h := H e
  have hleft : H = S h := by
    ext z
    calc
      H z = H (S z e) := by rw [comm z e, unit]
      _ = S z h := hH z e
      _ = S h z := comm z h
  have hc : ∀ a, Commute (S h) (S a) := by
    intro a
    rw [← hleft]
    ext z
    exact hH a z
  have dh : d h = 0 :=
    derivation_kills_central_multiplier S e comm unit frob d der h hc
  have hh : ⟪h, h⟫_ℝ = 0 := by
    have he : h = d.adjoint e := by simp [h, H, de]
    rw [he, LinearMap.adjoint_inner_left, ← he, dh, inner_zero_right]
  have hz : H = 0 := by
    rw [hleft, (inner_self_eq_zero (𝕜 := ℝ)).mp hh, map_zero]
  have hxy := congrArg (fun T : V →ₗ[ℝ] V => ⟪T x, y⟫_ℝ) hz
  simpa only [H, LinearMap.add_apply, inner_add_left, LinearMap.adjoint_inner_left,
    LinearMap.zero_apply, inner_zero_left, add_eq_zero_iff_eq_neg] using hxy

#print axioms derivation_skew_adjoint

end D5.S3.Quantum.Foundation.FrobeniusDerivation
