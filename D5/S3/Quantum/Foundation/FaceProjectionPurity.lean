/- GID: D5/S3/Quantum/Foundation/FaceProjectionPurity
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FaceProjectionPurity
   mirror-E: none(waiver:general-structural-mathematics)
   anchors: []
   utility: none
   digest: Full least confirmation forces purity of positive orthogonal face projections. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import Mathlib.Geometry.Convex.Cone.Face.Lattice
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
The cone, normalized base, extreme points and full proper-effect interval are those
of CircuitBalancedConfirmation. The symmetric positive definite pairing represents
the original least confirmers. Its self-duality and the positive orthogonal face
projection are explicit suppliers. No compatibility with the numerical values of
the ambient norm is imposed. All continuity uses the original finite dimensional
topology. Literature priority is not asserted.
-/

noncomputable section

namespace D5.S3.Quantum.Foundation.FaceProjectionPurity

open CircuitBalancedConfirmation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

private theorem diagonal_continuous (B : A →ₗ[ℝ] A →ₗ[ℝ] ℝ) :
    Continuous (fun x => B x x) := by
  let T : A →ₗ[ℝ] A →L[ℝ] ℝ := LinearMap.toContinuousLinearMap.toLinearMap.comp B
  exact T.continuous_of_finiteDimensional.clm_apply continuous_id

private theorem pairing_bound {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (B : A →ₗ[ℝ] A →ₗ[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (hK : IsCompact (base C u))
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hc : ∀ p : pure C u, confirms C u p (B p))
    {x y : A} (hx : x ∈ C) (hy : y ∈ C) : B x y ≤ u x * u y := by
  have hh := nonneg_on_cone (f := (u y) • u - B y) hK hu (fun p => ?_) x hx
  · simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hsym y x, sub_nonneg, mul_comm (u y)] using hh
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, (pure_mem p).2,
      mul_one, sub_nonneg, hsym y p]
    exact ((hc p).1 y hy).2

private theorem pure_locus {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (B : A →ₗ[ℝ] A →ₗ[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (hpos : ∀ x : A, x ≠ 0 → 0 < B x x)
    (hK : IsCompact (base C u))
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hc : ∀ p : pure C u, confirms C u p (B p)) :
    pure C u = {x | x ∈ base C u ∧ B x x = 1} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, (hc ⟨x, hx⟩).2⟩
  · rintro ⟨hx, hxx⟩
    have hb (y : A) (hy : y ∈ base C u) : B y y ≤ 1 := by
      simpa only [hy.2, mul_one] using pairing_bound B hsym hK hu hc hy.1 hy.1
    have hxy (y : A) (hy : y ∈ base C u) : B x y ≤ 1 := by
      simpa only [hx.2, hy.2, mul_one] using pairing_bound B hsym hK hu hc hx.1 hy.1
    have heq (y : A) (hy : y ∈ base C u) (h : B x y = 1) : y = x := by
      apply sub_eq_zero.mp
      by_contra hne
      have hp := hpos (y - x) hne
      simp only [map_sub, LinearMap.sub_apply] at hp
      rw [hsym y x, h, hxx] at hp
      linarith [hb y hy]
    refine ⟨hx, ?_⟩
    intro y hy z hz hseg
    obtain ⟨a, b, ha, hb', hab, he⟩ := hseg
    have hv : a * B x y + b * B x z = 1 := by
      rw [← map_smul, ← map_smul, ← map_add, he, hxx]
    have hxy1 : B x y = 1 := by
      have := hxy y hy
      have := hxy z hz
      nlinarith
    have hxz1 : B x z = 1 := by
      have := hxy y hy
      have := hxy z hz
      nlinarith
    exact (heq y hy hxy1).trans (heq z hz hxz1).symm

private theorem unit_representative (B : A →ₗ[ℝ] A →ₗ[ℝ] ℝ)
    (hpos : ∀ x : A, x ≠ 0 → 0 < B x x) (u : A →ₗ[ℝ] ℝ) :
    ∃ U : A, B U = u := by
  have hinj : Function.Injective B := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    by_contra hne
    have hh := hpos x hne
    have hz : B x = 0 := hx
    simp [hz] at hh
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Module.finrank_dual])).mp hinj u

private theorem augmented_cauchy (B : A →ₗ[ℝ] A →ₗ[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnon : ∀ x, 0 ≤ B x x)
    (a b : ℝ) (x y : A) :
    (a * b + B x y) ^ 2 ≤ (a ^ 2 + B x x) * (b ^ 2 + B y y) := by
  letI : PreInnerProductSpace.Core ℝ (ℝ × A) := {
    inner := fun v w => v.1 * w.1 + B v.2 w.2
    conj_inner_symm := by intro v w; simp only [RCLike.conj_to_real]; rw [hsym]; ring
    re_inner_nonneg := fun v => by simpa using add_nonneg (sq_nonneg v.1) (hnon v.2)
    add_left := by intro v w z; simp only [Prod.fst_add, Prod.snd_add, map_add,
      LinearMap.add_apply]; ring
    smul_left := by intro v w r; simp only [Prod.smul_fst, Prod.smul_snd, map_smul,
      LinearMap.smul_apply, smul_eq_mul, RCLike.conj_to_real]; ring }
  have hh := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℝ) (a, x) (b, y)
  change |a * b + B x y| * |b * a + B y x| ≤ _ at hh
  rw [hsym y x, mul_comm b a, ← sq_abs] at hh
  simpa only [sq_abs, RCLike.re_to_real, pow_two] using hh

end D5.S3.Quantum.Foundation.FaceProjectionPurity
