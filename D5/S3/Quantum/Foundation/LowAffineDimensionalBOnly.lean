/- GID: D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly
   generality: G
   mirror-B: none(waiver:registration-template-not-established)
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: A whole-base ball chart supplies an original proper antipodal effect.
-/

import D5.S3.Quantum.Foundation.WholePairBallConfirmation
import D5.S3.Quantum.Foundation.FinitePureSimplex
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
The full-base branch of the arbitrary-pure low-dimensional argument.  The
coordinate functional is defined on the chart direction, extended as a linear
map on the original carrier, and then normalized with the original unit.  The
properness proof is on the whole original cone; no restricted effect space or
finite pure carrier is introduced.
-/

noncomputable section

namespace D5.S3.Quantum.Foundation.LowAffineDimensionalBOnly

open CircuitBalancedConfirmation
open WholePairBallConfirmation
open FinitePureSimplex
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

private theorem chart_linear_injective {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    {p q : V} (b : BallChart C u p q) :
    Function.Injective b.param.linear := by
  intro x y hxy
  have hlin0 : b.param.linear (x - y) = 0 := by
    simpa [hxy] using b.param.linear_apply_vsub x y
  have hparam : b.param (x - y) - b.param 0 = 0 := by
    simpa [hlin0] using (b.param.linear_apply_vsub (x - y) 0).symm
  exact sub_eq_zero.mp (b.injective (sub_eq_zero.mp hparam))

private theorem chart_linear_coordinate {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    {p q : V} (b : BallChart C u p q) (n : EuclideanSpace ℝ (Fin b.dim))
    (hn : ‖n‖ = 1) :
    ∃ g : V →ₗ[ℝ] ℝ, ∀ s,
      g (b.param s - b.param 0) = ⟪n, s⟫ := by
  let E := EuclideanSpace ℝ (Fin b.dim)
  let ℓ : E →ₗ[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) n
  let e : E ≃ₗ[ℝ] LinearMap.range b.param.linear :=
    LinearEquiv.ofInjective b.param.linear (chart_linear_injective b)
  let f : LinearMap.range b.param.linear →ₗ[ℝ] ℝ :=
    ℓ.comp e.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨g, ?_⟩
  intro s
  have hmem : b.param.linear s ∈ LinearMap.range b.param.linear :=
    LinearMap.mem_range_self _ _
  have he : e s = ⟨b.param.linear s, hmem⟩ := rfl
  have hback : e.symm ⟨b.param.linear s, hmem⟩ = s := e.symm_apply_apply s
  have hgs : g (b.param.linear s) = ℓ s := by
    have hh := congrArg (fun k => k ⟨b.param.linear s, hmem⟩) hg
    change g (b.param.linear s) = ℓ (e.symm ⟨b.param.linear s, hmem⟩) at hh
    simpa [hback] using hh
  have hdiff : b.param s - b.param 0 = b.param.linear s := by
    simpa using (b.param.linear_apply_vsub s 0).symm
  rw [hdiff]
  simpa [ℓ, real_inner_comm] using hgs

/-- A whole-base ball chart gives the original proper effect separating every
coordinate antipodal pair.  The hypothesis `hwhole` is the full-base branch of
the source theorem: the selected entire pair face is the original base. -/
theorem ball_chart_antipodal_effect
    (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    {p q : V} (b : BallChart C u p q)
    (hwhole : pairBase C u p q = base C u)
    {n : EuclideanSpace ℝ (Fin b.dim)} (hn : ‖n‖ = 1) :
    ∃ f : V →ₗ[ℝ] ℝ,
      confirms C u (b.param n) f ∧ f (b.param (-n)) = 0 := by
  let E := EuclideanSpace ℝ (Fin b.dim)
  obtain ⟨g, hg⟩ := chart_linear_coordinate b n hn
  let α : ℝ := g (b.param 0)
  let f : V →ₗ[ℝ] ℝ :=
    (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • g - (α / 2 : ℝ) • u
  have hchart (s : E) (hs : ‖s‖ ≤ 1) : b.param s ∈ base C u := by
    rw [← hwhole, ← b.whole]
    exact ⟨s, by simpa using hs, rfl⟩
  have hformula (s : E) (hs : ‖s‖ ≤ 1) :
      f (b.param s) = (1 + ⟪n, s⟫) / 2 := by
    have hsbase := hchart s hs
    have h0base := hchart 0 (by simp)
    have hu_s : u (b.param s) = 1 := hsbase.2
    have hu_0 : u (b.param 0) = 1 := h0base.2
    have hgs := hg s
    dsimp [f, α]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hu_s, hu_0]
    have hgdiff : g (b.param s) - g (b.param 0) = ⟪n, s⟫ := by
      simpa [map_sub] using hgs
    linarith
  have hbound (s : E) (hs : ‖s‖ ≤ 1) :
      0 ≤ f (b.param s) ∧ f (b.param s) ≤ 1 := by
    rw [hformula s hs]
    have hi : |⟪n, s⟫| ≤ 1 := by
      calc
        |⟪n, s⟫| ≤ ‖n‖ * ‖s‖ := abs_real_inner_le_norm n s
        _ ≤ 1 := by simpa [hn] using hs
    constructor <;> linarith [abs_le.mp hi]
  have hproper : proper C u f := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hux : 0 < u x := hstrict x hx hx0
    let z : V := (u x)⁻¹ • x
    have hz : z ∈ base C u := normalized_mem hstrict hx hx0
    rw [← hwhole] at hz
    rw [← b.whole] at hz
    obtain ⟨s, hs, hzs⟩ := hz
    have hs' : ‖s‖ ≤ 1 := by simpa using hs
    have hfz := hbound s hs'
    have hxz : x = u x • z := by
      dsimp [z]
      rw [smul_smul, mul_inv_cancel₀ hux.ne', one_smul]
    have hfx : f x = u x * f z := by
      calc
        f x = f (u x • z) := congrArg f hxz
        _ = u x • f z := map_smul f (u x) z
        _ = u x * f z := by rfl
    have hfz' : 0 ≤ f z ∧ f z ≤ 1 := by
      rw [← hzs]
      exact hfz
    rw [hfx]
    constructor
    · exact mul_nonneg hux.le hfz'.1
    · simpa [mul_one] using (mul_le_mul_of_nonneg_left hfz'.2 hux.le)
  have hplus : f (b.param n) = 1 := by
    rw [hformula n hn.le]
    rw [real_inner_self_eq_norm_sq, hn]
    norm_num
  have hminus : f (b.param (-n)) = 0 := by
    rw [hformula (-n) (by simpa [hn] using hn.le)]
    rw [inner_neg_right, real_inner_self_eq_norm_sq, hn]
    norm_num
  exact ⟨f, ⟨hproper, hplus⟩, hminus⟩

/-! The preceding effect is consumed by the original antipodal predicate. -/

theorem allAntipodes_of_full_pair_balls
    (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hB : ∀ (p q : pure C u), p ≠ q →
      ∃ b : BallChart C u p q, pairBase C u p q = base C u) :
    allAntipodes C u := by
  intro p q hpq b n hn _
  obtain ⟨_, hwhole⟩ := hB p q hpq
  obtain ⟨f, hf, hz⟩ := ball_chart_antipodal_effect C u hclosed hstrict b hwhole hn
  exact ⟨f, hf, hz⟩

end D5.S3.Quantum.Foundation.LowAffineDimensionalBOnly
