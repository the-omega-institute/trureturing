/- GID: D5/S3/Quantum/Analysis/CStarTriangleEqualityLocalUnitization
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CStarTriangleEqualityLocalUnitization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangle-equality rigidity for complex C-star algebras. -/

/-
admission_basis: escape-witness
escape_witness: local_unitization_norm
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27516
Declarations (definition rows carry no proof-shape claim):
unitization_multiplier_injective: proof_shape: content; consumers: unitization_norm_eq_left_regular.
unitization_norm_eq_left_regular: proof_shape: content; consumers: local_unitization_norm.
localUnitizationMap: definition; consumers: local_unitization_norm, local_unitization_seminorm_scale.
local_unitization_norm: proof_shape: content; consumers: local_unitization_seminorm_scale.
local_unitization_seminorm_scale: proof_shape: content; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityHereditary.seminorm_local_corner_cross.
-/

import Mathlib.Analysis.CStarAlgebra.Multiplier
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

namespace D5.S3.Quantum.Analysis.CStarTriangleEqualityLocalUnitization

section

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The canonical unital multiplier representation is faithful if no identity exists. -/
private theorem unitization_multiplier_injective
    (hnu : ¬ ∃ q : B, ∀ b : B, q * b = b ∧ b * q = b) :
    Function.Injective (Unitization.starLift (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := B))) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hL (y : B) : x.fst • y + x.snd * y = 0 := by
    have h := congrArg (fun m : DoubleCentralizer ℂ B => m.fst y) hx
    change x.fst • y + x.snd * y = 0 at h
    exact h
  have hR (y : B) : x.fst • y + y * x.snd = 0 := by
    have h := congrArg (fun m : DoubleCentralizer ℂ B => m.snd y) hx
    change x.fst • y + y * x.snd = 0 at h
    exact h
  by_cases hc : x.fst = 0
  · have hs : x.snd = 0 := by
      have hs := hL (star x.snd)
      simp only [hc, zero_smul, zero_add] at hs
      apply norm_eq_zero.mp
      have hn := congrArg norm hs
      rw [CStarRing.norm_self_mul_star, norm_zero] at hn
      nlinarith [norm_nonneg x.snd]
    exact Unitization.ext hc hs
  · exfalso
    apply hnu
    refine ⟨(-x.fst⁻¹) • x.snd, fun y => ?_⟩
    have hLy : x.snd * y = -(x.fst • y) := eq_neg_of_add_eq_zero_right (hL y)
    have hRy : y * x.snd = -(x.fst • y) := eq_neg_of_add_eq_zero_right (hR y)
    constructor
    · rw [smul_mul_assoc, hLy, smul_neg, smul_smul]
      simp [hc]
    · rw [mul_smul_comm, hRy, smul_neg, smul_smul]
      simp [hc]

/-- In a genuinely nonunital C*-algebra the scalar coordinate is already detected by multiplication. -/
private theorem unitization_norm_eq_left_regular
    (hnu : ¬ ∃ q : B, ∀ b : B, q * b = b ∧ b * q = b)
    (x : Unitization ℂ B) :
    ‖x‖ = ‖algebraMap ℂ (B →L[ℂ] B) x.fst + ContinuousLinearMap.mul ℂ B x.snd‖ := by
  let Φ := Unitization.starLift (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := B))
  have hΦ : Function.Injective Φ := unitization_multiplier_injective hnu
  rw [← NonUnitalStarAlgHom.norm_map Φ hΦ x, ← DoubleCentralizer.norm_fst]
  rfl

/-- A contractive local identity gives the linear embedding of a unitization. -/
private def localUnitizationMap (φ : B →⋆ₙₐ[ℂ] A) (e : A) : Unitization ℂ B →ₗ[ℂ] A where
  toFun x := φ x.snd + x.fst • e
  map_add' x y := by simp only [Unitization.snd_add, Unitization.fst_add, map_add, add_smul]; module
  map_smul' c x := by
    simp only [Unitization.snd_smul, Unitization.fst_smul, map_smul, smul_add, smul_smul]
    rfl

/-- The local-identity embedding is isometric; it need not be multiplicative. -/
private theorem local_unitization_norm (φ : B →⋆ₙₐ[ℂ] A) (hφ : Function.Injective φ)
    (hnu : ¬ ∃ q : B, ∀ b : B, q * b = b ∧ b * q = b)
    (e : A) (he : ‖e‖ ≤ 1) (heL : ∀ b : B, e * φ b = φ b)
    (x : Unitization ℂ B) : ‖localUnitizationMap φ e x‖ = ‖x‖ := by
  have hnorm (b : B) : ‖φ b‖ = ‖b‖ := NonUnitalStarAlgHom.norm_map φ hφ b
  apply le_antisymm
  · let Ψ := Unitization.starMap φ
    have hΨ : Function.Injective Ψ := Unitization.starMap_injective hφ
    have heq : ((localUnitizationMap φ e x : A) : Unitization ℂ A) =
        (e : Unitization ℂ A) * Ψ x := by
      change ((φ x.snd + x.fst • e : A) : Unitization ℂ A) =
        (e : Unitization ℂ A) * (algebraMap ℂ (Unitization ℂ A) x.fst +
          (φ x.snd : Unitization ℂ A))
      simp only [Unitization.inr_add, Unitization.inr_smul, Algebra.algebraMap_eq_smul_one,
        mul_add, mul_smul_comm, mul_one, ← Unitization.inr_mul, heL]
      rw [add_comm]
    calc
      ‖localUnitizationMap φ e x‖ = ‖((localUnitizationMap φ e x : A) : Unitization ℂ A)‖ :=
        (Unitization.norm_inr _).symm
      _ = ‖(e : Unitization ℂ A) * Ψ x‖ := congrArg norm heq
      _ ≤ ‖(e : Unitization ℂ A)‖ * ‖Ψ x‖ := norm_mul_le _ _
      _ ≤ 1 * ‖x‖ := by
        rw [Unitization.norm_inr, NonUnitalStarAlgHom.norm_map Ψ hΨ]
        exact mul_le_mul_of_nonneg_right he (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  · rw [unitization_norm_eq_left_regular hnu]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro b
    have heq : φ ((algebraMap ℂ (B →L[ℂ] B) x.fst +
        ContinuousLinearMap.mul ℂ B x.snd) b) = localUnitizationMap φ e x * φ b := by
      change φ (x.fst • b + x.snd * b) = (φ x.snd + x.fst • e) * φ b
      rw [map_add, map_smul, map_mul, add_mul, smul_mul_assoc, heL, add_comm]
    calc
      ‖(algebraMap ℂ (B →L[ℂ] B) x.fst + ContinuousLinearMap.mul ℂ B x.snd) b‖ =
          ‖φ ((algebraMap ℂ (B →L[ℂ] B) x.fst + ContinuousLinearMap.mul ℂ B x.snd) b)‖ :=
        (hnorm _).symm
      _ = ‖localUnitizationMap φ e x * φ b‖ := congrArg norm heq
      _ ≤ ‖localUnitizationMap φ e x‖ * ‖φ b‖ := norm_mul_le _ _
      _ = ‖localUnitizationMap φ e x‖ * ‖b‖ := by rw [hnorm]

end

section

/-- The unital seminorm theorem transfers through an isometric local unitization. -/
theorem local_unitization_seminorm_scale {A B : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : B →⋆ₙₐ[ℂ] A) (hφ : Function.Injective φ)
    (hnu : ¬ ∃ q : B, ∀ b : B, q * b = b ∧ b * q = b)
    (e : A) (he : ‖e‖ ≤ 1) (heL : ∀ b : B, e * φ b = φ b)
    (hrigidity : ∀ q : Seminorm ℂ (Unitization ℂ B),
      (∀ x y : Unitization ℂ B, ‖x + y‖ = ‖x‖ + ‖y‖ → q (x + y) = q x + q y) →
      ∀ x : Unitization ℂ B, q x = q 1 * ‖x‖)
    (p : Seminorm ℂ A)
    (hp : ∀ a b : A, ‖a + b‖ = ‖a‖ + ‖b‖ → p (a + b) = p a + p b)
    (b : B) : p (φ b) = p e * ‖b‖ := by
  let J : Unitization ℂ B →ₗᵢ[ℂ] A :=
    { toLinearMap := localUnitizationMap φ e
      norm_map' := local_unitization_norm φ hφ hnu e he heL }
  let q : Seminorm ℂ (Unitization ℂ B) := p.comp J.toLinearMap
  have hq : ∀ x y : Unitization ℂ B, ‖x + y‖ = ‖x‖ + ‖y‖ → q (x + y) = q x + q y := by
    intro x y hxy
    change p (J (x + y)) = p (J x) + p (J y)
    rw [map_add]
    apply hp
    simpa only [← map_add, J.norm_map] using hxy
  have hJone : J 1 = e := by
    change φ (1 : Unitization ℂ B).snd + (1 : Unitization ℂ B).fst • e = e
    simp
  have hJb : J (b : Unitization ℂ B) = φ b := by
    change φ (b : Unitization ℂ B).snd + (b : Unitization ℂ B).fst • e = φ b
    simp
  have hr := hrigidity q hq (b : Unitization ℂ B)
  change p (J (b : Unitization ℂ B)) = p (J 1) * ‖(b : Unitization ℂ B)‖ at hr
  simpa only [hJb, hJone, Unitization.norm_inr] using hr

end

end D5.S3.Quantum.Analysis.CStarTriangleEqualityLocalUnitization
