/- GID: D5/S3/Topology/OrderUnitCompletion
   generality: G
   mirror-B: D5/B/S3/Topology/OrderUnitCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Topology/OrderUnitNorm]
   utility: none
   digest: Completion preserves the specified order norm, cone and interior unit faithfully. -/

module

public import D5.S3.Topology.OrderUnitNorm
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Convex.Cone.Closure

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology Pointwise
open Set UniformSpace

namespace D5.S3.Topology.OrderUnitNorm.Data

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : OrderUnitNorm.Data E)

/-- The closure of the original cone under the canonical linear isometric embedding. -/
def completedCone : ConvexCone ℝ (Completion E) :=
  (A.cone.map (Completion.toComplₗᵢ (𝕜 := ℝ) (E := E)).toLinearMap).closure

private lemma coe_mem_completedCone (a : E) :
    (a : Completion E) ∈ A.completedCone ↔ a ∈ A.cone := by
  change (a : Completion E) ∈ closure (((↑) : E → Completion E) '' (A.cone : Set E)) ↔ _
  have h := (Completion.isUniformEmbedding_coe E).isEmbedding.closure_eq_preimage_closure_image
    (A.cone : Set E)
  rw [← Set.mem_preimage, ← h, A.closed.closure_eq]

private lemma positive_difference_bound (hnorm : ∀ a : E, ‖a‖ = A.orderNorm a)
    {b c : E} (hb : b ∈ A.cone) (hc : c ∈ A.cone) : ‖b - c‖ ≤ ‖b + c‖ := by
  rw [hnorm, hnorm]
  apply (A.norm_le_iff _ _).mpr
  have h := (A.norm_le_iff (b + c) (A.orderNorm (b + c))).mp le_rfl
  refine ⟨h.1, ?_, ?_⟩
  · convert A.cone.add_mem h.2.1 (A.cone.add_mem hc hc) using 1 <;> module
  · convert A.cone.add_mem h.2.1 (A.cone.add_mem hb hb) using 1 <;> module

private lemma completed_positive_difference_bound (hnorm : ∀ a : E, ‖a‖ = A.orderNorm a)
    {y z : Completion E} (hy : y ∈ A.completedCone) (hz : z ∈ A.completedCone) :
    ‖y - z‖ ≤ ‖y + z‖ := by
  let s : Set (Completion E) := ((↑) : E → Completion E) '' (A.cone : Set E)
  have hbase : ∀ b ∈ s, ∀ c ∈ s, ‖b - c‖ ≤ ‖b + c‖ := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    simpa only [← Completion.coe_sub, ← Completion.coe_add, Completion.norm_coe] using
      A.positive_difference_bound hnorm hb hc
  have hfirst : ∀ b ∈ s, ∀ c ∈ closure s, ‖b - c‖ ≤ ‖b + c‖ := by
    intro b hb
    exact closure_minimal (hbase b hb) (isClosed_le (by fun_prop) (by fun_prop))
  exact (closure_minimal (fun b hb => hfirst b hb z hz)
    (isClosed_le (by fun_prop) (by fun_prop))) hy

private lemma completed_norm_endpoints (hnorm : ∀ a : E, ‖a‖ = A.orderNorm a)
    (x : Completion E) :
    ‖x‖ • (A.unit : Completion E) - x ∈ A.completedCone ∧
      ‖x‖ • (A.unit : Completion E) + x ∈ A.completedCone := by
  apply Completion.induction_on x
  · exact (isClosed_closure.preimage (by fun_prop)).inter
      (isClosed_closure.preimage (by fun_prop))
  · intro a
    have h := (A.norm_le_iff a (A.orderNorm a)).mp le_rfl
    constructor
    · have hh := (A.coe_mem_completedCone (‖a‖ • A.unit - a)).mpr (by simpa [hnorm] using h.2.1)
      simpa only [Completion.norm_coe, Completion.coe_sub, Completion.coe_smul] using hh
    · have hh := (A.coe_mem_completedCone (‖a‖ • A.unit + a)).mpr (by simpa [hnorm] using h.2.2)
      simpa only [Completion.norm_coe, Completion.coe_add, Completion.coe_smul] using hh

private lemma completed_norm_le_iff (hnorm : ∀ a : E, ‖a‖ = A.orderNorm a)
    (x : Completion E) (r : ℝ) :
    ‖x‖ ≤ r ↔ 0 ≤ r ∧ r • (A.unit : Completion E) - x ∈ A.completedCone ∧
      r • (A.unit : Completion E) + x ∈ A.completedCone := by
  have hu : (A.unit : Completion E) ∈ A.completedCone :=
    (A.coe_mem_completedCone A.unit).mpr (interior_subset A.interior_unit)
  constructor
  · intro hr
    have hd : (r - ‖x‖) • (A.unit : Completion E) ∈ A.completedCone := by
      rcases (sub_nonneg.mpr hr).eq_or_lt with he | he
      · rw [← he, zero_smul]
        exact (A.coe_mem_completedCone 0).mpr A.zero_mem
      · exact A.completedCone.smul_mem he hu
    have hx := A.completed_norm_endpoints hnorm x
    refine ⟨(norm_nonneg x).trans hr, ?_, ?_⟩
    · convert A.completedCone.add_mem hx.1 hd using 1 <;> module
    · convert A.completedCone.add_mem hx.2 hd using 1 <;> module
  · rintro ⟨hr, hm, hp⟩
    have h := A.completed_positive_difference_bound hnorm hm hp
    have he₁ : (r • (A.unit : Completion E) - x) -
        (r • (A.unit : Completion E) + x) = -(2 : ℝ) • x := by module
    have he₂ : (r • (A.unit : Completion E) - x) +
        (r • (A.unit : Completion E) + x) = (2 * r) • (A.unit : Completion E) := by module
    rw [he₁, he₂, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (mul_nonneg (by norm_num) hr),
      Completion.norm_coe] at h
    have hunit : ‖A.unit‖ ≤ 1 := by
      rw [hnorm]
      apply (A.norm_le_iff _ _).mpr
      exact ⟨zero_le_one, by simpa using A.zero_mem,
        by simpa using A.cone.add_mem (interior_subset A.interior_unit) (interior_subset A.interior_unit)⟩
    have hh := mul_le_mul_of_nonneg_left hunit (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr)
    nlinarith

/-- Order-unit data on the original norm completion, retaining the closed image cone and unit. -/
def completedData (hnorm : ∀ a : E, ‖a‖ = A.orderNorm a) : OrderUnitNorm.Data (Completion E) where
  cone := A.completedCone
  unit := (A.unit : Completion E)
  zero_mem := (A.coe_mem_completedCone 0).mpr A.zero_mem
  closed := isClosed_closure
  salient := by
    intro x hx hne hn
    have h := (A.completed_norm_le_iff hnorm x 0).mpr
      ⟨le_rfl, by simpa using hn, by simpa using hx⟩
    exact hne (norm_eq_zero.mp (le_antisymm h (norm_nonneg x)))
  interior_unit := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Metric.ball_mem_nhds (A.unit : Completion E) zero_lt_one)
    intro x hx
    have hnormx : ‖x - (A.unit : Completion E)‖ ≤ 1 :=
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hx : ‖x - (A.unit : Completion E)‖ < 1).le
    have h := (A.completed_norm_le_iff hnorm (x - (A.unit : Completion E)) 1).mp hnormx
    simpa only [one_smul, add_sub_cancel] using h.2.2

/-- The exact completed order intervals, norm agreement and faithful pullback of the original cone.
All real radii and the zero-dimensional space are included. -/
theorem faithful_completion (hnorm : ∀ a : E, ‖a‖ = A.orderNorm a) :
    (∀ x : Completion E, ∀ r : ℝ, ‖x‖ ≤ r ↔
      0 ≤ r ∧ r • (A.completedData hnorm).unit - x ∈ (A.completedData hnorm).cone ∧
        r • (A.completedData hnorm).unit + x ∈ (A.completedData hnorm).cone) ∧
    (∀ x : Completion E, (A.completedData hnorm).orderNorm x = ‖x‖) ∧
    (∀ a : E, (Completion.toComplₗᵢ (𝕜 := ℝ) (E := E)) a ∈
      (A.completedData hnorm).cone ↔ a ∈ A.cone) := by
  refine ⟨A.completed_norm_le_iff hnorm, ?_, A.coe_mem_completedCone⟩
  intro x
  apply le_antisymm
  · apply ((A.completedData hnorm).norm_le_iff x ‖x‖).mpr
    exact (A.completed_norm_le_iff hnorm x ‖x‖).mp le_rfl
  · apply (A.completed_norm_le_iff hnorm x ((A.completedData hnorm).orderNorm x)).mpr
    exact ((A.completedData hnorm).norm_le_iff x _).mp le_rfl

end D5.S3.Topology.OrderUnitNorm.Data
