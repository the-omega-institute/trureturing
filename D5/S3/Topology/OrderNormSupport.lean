/- GID: D5/S3/Topology/OrderNormSupport
   generality: G
   mirror-B: D5/B/S3/Topology/OrderNormSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Gauge]
   utility: none
   digest: Positive normalized order-norm support on the original carrier. -/

module

public import D5.S3.Topology.OrderUnitNorm

/-! A positive norm-support functional supplied by the original order-unit cone.
The source carrier remains arbitrary and possibly incomplete. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Pointwise Topology

namespace D5.S3.Topology.OrderUnitNorm.Data

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (A : Data E)

/-- A positive normalized order-norm support on the entire original carrier.
No completeness or finite dimension is required. -/
theorem positive_norm_support (a : E) (ha : a ≠ 0) :
    ∃ β : E →ₗ[ℝ] ℝ, (∀ x ∈ A.cone, 0 ≤ β x) ∧ β A.unit = 1 ∧
      (∀ x, |β x| ≤ A.orderNorm x) ∧ |β a| = A.orderNorm a := by
  let r := A.orderNorm a
  have hr0 : 0 ≤ r := A.norm_nonneg a
  have hr : 0 < r := lt_of_le_of_ne hr0 (Ne.symm (fun h => ha ((A.norm_zero_iff a).mp h)))
  have hz := A.norm_attained a
  have hboundary : r • A.unit - a ∉ interior (A.cone : Set E) ∨
      r • A.unit + a ∉ interior (A.cone : Set E) := by
    by_contra hn
    push_neg at hn
    let V : Set ℝ := {s | s • A.unit - a ∈ interior (A.cone : Set E) ∧
      s • A.unit + a ∈ interior (A.cone : Set E)}
    have hV : IsOpen V :=
      (isOpen_interior.preimage ((continuous_id.smul continuous_const).sub continuous_const)).inter
        (isOpen_interior.preimage ((continuous_id.smul continuous_const).add continuous_const))
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV r hn
    let d := min r ε / 2
    have hd : 0 < d := by dsimp [d]; positivity
    have hdr : d ≤ r := by dsimp [d]; have := min_le_left r ε; linarith
    have hde : d < ε := by dsimp [d]; have := min_le_right r ε; linarith
    have hv : r - d ∈ V := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      have he : |r - d - r| = d := by rw [show r - d - r = -d by ring, abs_neg, abs_of_pos hd]
      simpa only [he] using hde)
    have hb : A.orderNorm a ≤ r - d :=
      (A.norm_le_iff a (r - d)).mpr ⟨by linarith, interior_subset hv.1, interior_subset hv.2⟩
    change r ≤ r - d at hb
    linarith
  have hs : ∃ β : E →L[ℝ] ℝ, (∀ x ∈ A.cone, 0 ≤ β x) ∧
      0 < β A.unit ∧ |β a| = β A.unit * r := by
    rcases hboundary with hm | hp
    · obtain ⟨β, hβ, he, hmass⟩ := A.boundary_support _ hz.2.1 hm
      refine ⟨β, hβ, hmass, ?_⟩
      simp only [map_sub, map_smul, smul_eq_mul] at he
      rw [show β a = β A.unit * r by nlinarith only [he], abs_of_nonneg (mul_nonneg hmass.le hr0)]
    · obtain ⟨β, hβ, he, hmass⟩ := A.boundary_support _ hz.2.2 hp
      refine ⟨β, hβ, hmass, ?_⟩
      simp only [map_add, map_smul, smul_eq_mul] at he
      rw [show β a = -(β A.unit * r) by nlinarith only [he], abs_neg,
        abs_of_nonneg (mul_nonneg hmass.le hr0)]
  obtain ⟨β, hβ, hmass, hs⟩ := hs
  let γ : E →ₗ[ℝ] ℝ := (β A.unit)⁻¹ • β.toLinearMap
  have hγ : ∀ x ∈ A.cone, 0 ≤ γ x := by
    intro x hx
    exact mul_nonneg (inv_nonneg.mpr hmass.le) (hβ x hx)
  have hγu : γ A.unit = 1 := by simp [γ, hmass.ne']
  refine ⟨γ, hγ, hγu, ?_, ?_⟩
  · intro x
    simpa only [hγu, one_mul] using A.positive_bound γ hγ x
  · change |(β A.unit)⁻¹ * β a| = r
    rw [abs_mul, abs_inv, abs_of_pos hmass, hs]
    field_simp

end D5.S3.Topology.OrderUnitNorm.Data
