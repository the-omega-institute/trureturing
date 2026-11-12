/- GID: D5/S3/Quantum/Foundation/WholePairBallConfirmation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/WholePairBallConfirmation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Whole minimal-face balls and common positive supports construct least confirmation. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import Mathlib.Geometry.Convex.Cone.Face.Lattice
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The base, pure points, proper interval and least-confirmation predicate are the
original CircuitBalancedConfirmation objects. Pair bases use every cone face,
not a selected patch. Ball dimensions may vary and include one.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.WholePairBallConfirmation

open CircuitBalancedConfirmation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The entire base of the smallest original cone face containing both points. -/
def pairBase (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p q : V) : Set V :=
  {x | x ∈ base C u ∧ ∀ F : C.Face, p ∈ F → q ∈ F → x ∈ F}

/-- An injective affine parametrization of the entire pair base by a closed ball. -/
structure BallChart (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p q : V) where
  dim : ℕ
  dim_pos : 0 < dim
  param : EuclideanSpace ℝ (Fin dim) →ᵃ[ℝ] V
  injective : Function.Injective param
  whole : param '' Metric.closedBall 0 1 = pairBase C u p q

/-- All distinct global pure pairs have entire finite ball bases. -/
def wholePairBalls (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ p q : pure C u, p ≠ q → Nonempty (BallChart C u p q)

/-- One positive functional per pure point vanishes at every chart antipode.
No proper upper bound or leastness is assumed. -/
def commonSupport (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ p : pure C u, ∃ g : V →ₗ[ℝ] ℝ,
    (∀ x ∈ C, 0 ≤ g x) ∧ 0 < g p ∧
    ∀ (q : pure C u), p ≠ q → ∀ b : BallChart C u p q,
      ∀ n, ‖n‖ = 1 → b.param n = p → g (b.param (-n)) = 0

private theorem affine_extreme_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ᵃ[ℝ] V) (hf : Function.Injective f) (S : Set E) (x : E) :
    f x ∈ (f '' S).extremePoints ℝ ↔ x ∈ S.extremePoints ℝ := by
  constructor
  · rintro ⟨hx, he⟩
    refine ⟨(hf.mem_set_image).mp hx, ?_⟩
    intro a ha b hb hab
    apply hf
    exact he ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      ((image_openSegment ℝ f a b) ▸ Set.mem_image_of_mem f hab)
  · rintro ⟨hx, he⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    apply congrArg f
    apply he ha hb
    rw [← image_openSegment ℝ f a b] at hab
    exact hf.mem_set_image.mp hab

private theorem chart_mem {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p q : V}
    (b : BallChart C u p q) {s} (hs : ‖s‖ ≤ 1) : b.param s ∈ pairBase C u p q := by
  rw [← b.whole]
  exact ⟨s, by simpa using hs, rfl⟩

private theorem chart_pure_norm {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p q : V}
    (b : BallChart C u p q) {s} (hs : ‖s‖ ≤ 1)
    (hp : b.param s ∈ pure C u) : ‖s‖ = 1 := by
  letI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  have he : b.param s ∈ (b.param '' Metric.closedBall 0 1).extremePoints ℝ := by
    refine ⟨⟨s, by simpa using hs, rfl⟩, ?_⟩
    intro x hx y hy hxy
    exact hp.2 ((b.whole ▸ hx).1) ((b.whole ▸ hy).1) hxy
  have hh := (affine_extreme_iff b.param b.injective _ s).mp he
  rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere] at hh
  simpa using hh

private theorem affine_riesz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →ᵃ[ℝ] ℝ) :
    ∃ v : E, ∀ s, f s = f 0 + ⟪v, s⟫ := by
  let L := f.linear.toContinuousLinearMap
  refine ⟨(InnerProductSpace.toDual ℝ E).symm L, fun s => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  simpa [L, add_comm] using congrFun f.decomp s

private theorem affine_nonneg_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a : ℝ} {v : E}
    (h : ∀ s : E, ‖s‖ ≤ 1 → 0 ≤ a + ⟪v, s⟫) : ‖v‖ ≤ a := by
  by_cases hv : v = 0
  · simpa [hv] using h 0 (by simp)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hs : ‖-(‖v‖⁻¹ • v)‖ ≤ 1 := by
    simp [norm_smul, abs_inv, abs_of_pos hvpos, hvpos.ne']
  have hh := h (-(‖v‖⁻¹ • v)) hs
  simp only [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq] at hh
  have he : ‖v‖⁻¹ * ‖v‖ ^ 2 = ‖v‖ := by field_simp; ring
  rw [he] at hh
  linarith

private theorem affine_zero_antipode {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E →ᵃ[ℝ] ℝ) {n : E} (hn : ‖n‖ = 1)
    (hpos : ∀ s, ‖s‖ ≤ 1 → 0 ≤ f s) (hz : f (-n) = 0) :
    ∀ s, f s = f n / 2 * (1 + ⟪n, s⟫) := by
  obtain ⟨v, hv⟩ := affine_riesz f
  have hbound := affine_nonneg_bound (fun s hs => by rw [← hv]; exact hpos s hs)
  have hzero : f 0 = ⟪v, n⟫ := by rw [hv] at hz; simpa using hz
  have hcs : ⟪v, n⟫ ≤ ‖v‖ := by simpa [hn] using real_inner_le_norm v n
  have heq : f 0 = ‖v‖ := le_antisymm (hzero.trans_le hcs) hbound
  have halign : v = ‖v‖ • n := by
    have hh := inner_eq_norm_mul_iff_real.mp (show ⟪v, n⟫ = ‖v‖ * ‖n‖ by rw [hn, mul_one, ← heq, hzero])
    simpa [hn] using hh
  have hfn : f n = 2 * f 0 := by rw [hv, ← hzero]; ring
  intro s
  rw [hv, halign, inner_smul_left, ← heq, hfn]
  ring

end D5.S3.Quantum.Foundation.WholePairBallConfirmation
