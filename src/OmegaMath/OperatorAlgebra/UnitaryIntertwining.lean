import OmegaBuild.Commands
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Tactic

/-! Omega original.
Schur's intertwiner conclusion for families of unitary Hilbert-space operators. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped InnerProductSpace
open ContinuousLinearMap

namespace Omega.UnitaryIntertwining

variable {X Y S : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- A family has scalar commutant if every operator commuting with its members is scalar. -/
def ScalarCommutant {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : S → E →L[ℂ] E) : Prop :=
  ∀ T : E →L[ℂ] E, (∀ s, T * U s = U s * T) → ∃ c : ℂ, T = c • 1

/-- A nonzero bounded intertwiner of irreducible unitary families is proportional to a unitary. -/
theorem irreducible_intertwiner_isometry_or_zero
    (U : S → X →L[ℂ] X) (V : S → Y →L[ℂ] Y)
    (hU : ∀ s, U s * (U s).adjoint = 1) (hV : ∀ s, (V s).adjoint * V s = 1)
    (hscalarU : ScalarCommutant U) (hscalarV : ScalarCommutant V)
    (T : X →L[ℂ] Y) (hT : ∀ s, T.comp (U s) = (V s).comp T) :
    T = 0 ∨ ∃ (c : ℂ) (E : X ≃ₗᵢ[ℂ] Y), c ≠ 0 ∧
      T = c • E.toLinearIsometry.toContinuousLinearMap ∧
      ∀ s x, E (U s x) = V s (E x) := by
  by_cases ht : T = 0
  · exact Or.inl ht
  right
  have hadj (s : S) : T.adjoint.comp (V s) = (U s).comp T.adjoint := by
    have hh := congrArg adjoint (hT s)
    rw [adjoint_comp, adjoint_comp] at hh
    have hc (x : X) : U s ((U s).adjoint x) = x := DFunLike.congr_fun (hU s) x
    have hd (y : Y) : (V s).adjoint (V s y) = y := DFunLike.congr_fun (hV s) y
    ext y
    have hh' := DFunLike.congr_fun hh (V s y)
    change (U s).adjoint (T.adjoint (V s y)) = T.adjoint ((V s).adjoint (V s y)) at hh'
    rw [hd] at hh'
    change T.adjoint (V s y) = U s (T.adjoint y)
    rw [← hh', hc]
  have hT' (s : S) (x : X) : T (U s x) = V s (T x) := DFunLike.congr_fun (hT s) x
  have ha' (s : S) (y : Y) : T.adjoint (V s y) = U s (T.adjoint y) :=
    DFunLike.congr_fun (hadj s) y
  obtain ⟨a, ha⟩ := hscalarU (T.adjoint.comp T) (fun s => by
    ext x
    change T.adjoint (T (U s x)) = U s (T.adjoint (T x))
    rw [hT', ha'])
  obtain ⟨b, hb⟩ := hscalarV (T.comp T.adjoint) (fun s => by
    ext y
    change T (T.adjoint (V s y)) = V s (T (T.adjoint y))
    rw [ha', hT'])
  obtain ⟨x₀, hx₀⟩ : ∃ x : X, T x ≠ 0 := by
    by_contra! h
    exact ht (ext fun x => by simpa using h x)
  have hnorm (x : X) : ‖T x‖ ^ 2 = a.re * ‖x‖ ^ 2 := by
    have h := DFunLike.congr_fun ha x
    change T.adjoint (T x) = a • x at h
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← adjoint_inner_right, h, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hap : 0 < a.re := by
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hn (sq_nonneg _)))
      (hnorm x₀ ▸ pow_pos (norm_pos_iff.mpr hx₀) 2)
  let c := Real.sqrt a.re
  have hc : 0 < c := Real.sqrt_pos.mpr hap
  have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hbn : b ≠ 0 := by
    intro hb0
    have h := DFunLike.congr_fun hb (T x₀)
    change T (T.adjoint (T x₀)) = b • T x₀ at h
    have hx := DFunLike.congr_fun ha x₀
    change T.adjoint (T x₀) = a • x₀ at hx
    rw [hx, map_smul, hb0, zero_smul] at h
    exact (smul_eq_zero.mp h).elim (fun hz => by simp [hz] at hap) hx₀
  let L : X →ₗᵢ[ℂ] Y :=
    { toLinearMap := ((c : ℂ)⁻¹ • T).toLinearMap
      norm_map' := fun x => by
        change ‖(c : ℂ)⁻¹ • T x‖ = ‖x‖
        have hy : ‖T x‖ = c * ‖x‖ := by
          apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
          rw [hnorm, mul_pow, Real.sq_sqrt hap.le]
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le, hy,
          ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] }
  have hsurj : Function.Surjective L := by
    intro y
    refine ⟨((c : ℂ) * b⁻¹) • T.adjoint y, ?_⟩
    have h := DFunLike.congr_fun hb y
    change T (T.adjoint y) = b • y at h
    change (c : ℂ)⁻¹ • T (((c : ℂ) * b⁻¹) • T.adjoint y) = y
    rw [map_smul, h, smul_smul, smul_smul]
    have hc' : (c : ℂ)⁻¹ * ((c : ℂ) * b⁻¹) * b = 1 := by
      rw [← mul_assoc, inv_mul_cancel₀ hcn, one_mul, inv_mul_cancel₀ hbn]
    rw [hc', one_smul]
  let E := LinearIsometryEquiv.ofSurjective L hsurj
  refine ⟨c, E, hcn, ?_, ?_⟩
  · ext x
    change T x = (c : ℂ) • ((c : ℂ)⁻¹ • T x)
    rw [smul_smul, mul_inv_cancel₀ hcn, one_smul]
  · intro s x
    change (c : ℂ)⁻¹ • T (U s x) = V s ((c : ℂ)⁻¹ • T x)
    rw [hT', map_smul]

end Omega.UnitaryIntertwining
