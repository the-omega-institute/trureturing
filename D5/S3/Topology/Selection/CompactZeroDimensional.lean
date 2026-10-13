/- GID: D5/S3/Topology/Selection/CompactZeroDimensional
   generality: G
   mirror-B: D5/B/S3/Topology/Selection/CompactZeroDimensional
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact zero-dimensional closed fibers admit continuous prescribed-point selections. -/

import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Compact zero-dimensional continuous selection

Michael's classical selection principle for a compact Hausdorff totally
disconnected domain and a complete metric target. The domain needs no metric
or countability assumptions. Empty domains and empty targets are allowed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter TopologicalSpace
open scoped Topology

namespace D5.S3.Topology.Selection.CompactZeroDimensional

universe u v

variable {B : Type u} {K : Type v}
variable [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable [TotallyDisconnectedSpace B] [MetricSpace K]

omit [MetricSpace K] in
/-- Assign values to the cells of an existing finite disjoint clopen refinement.
Each assigned value comes from an open-cover member containing that cell. -/
private lemma locally_constant_subordinate (U : B → Opens B)
    (hU : ∀ b, b ∈ U b) (k : B → K) :
    ∃ a : LocallyConstant B K, ∀ b, ∃ c, b ∈ U c ∧ a b = k c := by
  classical
  have cover : IsOpenCover U := IsOpenCover.of_sets (fun b => (U b).isOpen) <| by
    ext b
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨b, hU b⟩
  obtain ⟨n, W, hW, hcover, hdis⟩ :=
    cover.exists_finite_nonempty_disjoint_clopen_cover
  have unique (b : B) : ∃! j, b ∈ W j := by
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover (mem_univ b))
    refine ⟨j, hj, fun i hi => hdis.eq ?_⟩
    simpa [← Clopens.coe_disjoint, not_disjoint_iff] using! ⟨b, hi, hj⟩
  choose cell hcell huniq using unique
  choose c hc using fun j => (hW j).2
  let a : B → K := fun b => k (c (cell b))
  have ha : IsLocallyConstant a := by
    refine (IsLocallyConstant.iff_exists_open a).2 fun b =>
      ⟨W (cell b), (W (cell b)).isOpen, hcell b, ?_⟩
    intro x hx
    have heq : cell x = cell b := (huniq x (cell b) hx).symm
    simp only [a, heq]
  exact ⟨⟨a, ha⟩, fun b => ⟨c (cell b), hc _ (hcell b), rfl⟩⟩

/-- Start the approximation with one actual fiber point per selected open cell. -/
private lemma initial_approximation (Phi : B → Set K)
    (hne : ∀ b, (Phi b).Nonempty) (hlsc : LowerHemicontinuous Phi)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : LocallyConstant B K,
      ∀ b, ∃ k ∈ Phi b, dist (a b) k < ε := by
  classical
  choose k hk using hne
  let U : B → Opens B := fun b =>
    ⟨{x | (Phi x ∩ Metric.ball (k b) ε).Nonempty},
      (lowerHemicontinuous_iff_isOpen_inter_nonempty.mp hlsc) _ Metric.isOpen_ball⟩
  have hU : ∀ b, b ∈ U b := fun b =>
    ⟨k b, hk b, Metric.mem_ball_self hε⟩
  obtain ⟨a, ha⟩ := locally_constant_subordinate U hU k
  refine ⟨a, fun b => ?_⟩
  obtain ⟨c, hc, heq⟩ := ha b
  obtain ⟨z, hz, hdist⟩ := hc
  refine ⟨z, hz, ?_⟩
  rw [heq, dist_comm]
  exact hdist

/-- Refine the fiber error while keeping the new value within the old error.
The equality fiber of the old locally constant map is part of the cover. -/
private lemma refine_approximation (Phi : B → Set K)
    (hlsc : LowerHemicontinuous Phi) (a : LocallyConstant B K)
    {δ ε : ℝ} (hε : 0 < ε)
    (ha : ∀ b, ∃ k ∈ Phi b, dist (a b) k < δ) :
    ∃ a' : LocallyConstant B K,
      (∀ b, ∃ k ∈ Phi b, dist (a' b) k < ε) ∧
      ∀ b, dist (a b) (a' b) ≤ δ := by
  classical
  choose k hk hdist using ha
  let U : B → Opens B := fun b =>
    ⟨{x | a x = a b} ∩ {x | (Phi x ∩ Metric.ball (k b) ε).Nonempty},
      (a.isLocallyConstant.isOpen_fiber (a b)).inter
        ((lowerHemicontinuous_iff_isOpen_inter_nonempty.mp hlsc) _ Metric.isOpen_ball)⟩
  have hU : ∀ b, b ∈ U b := fun b =>
    ⟨rfl, k b, hk b, Metric.mem_ball_self hε⟩
  obtain ⟨a', ha'⟩ := locally_constant_subordinate U hU k
  refine ⟨a', ?_, ?_⟩
  · intro b
    obtain ⟨c, hc, heq⟩ := ha' b
    obtain ⟨z, hz, hball⟩ := hc.2
    refine ⟨z, hz, ?_⟩
    rw [heq, dist_comm]
    exact hball
  · intro b
    obtain ⟨c, hc, heq⟩ := ha' b
    rw [heq, hc.1]
    exact (hdist c).le

/-- Michael's compact zero-dimensional selection theorem with the literal
open-hitting-set hypothesis. No nonemptiness instance is required on either
carrier; in particular the empty function is included. -/
theorem exists_continuous_selection [CompleteSpace K] (Phi : B → Set K)
    (hne : ∀ b, (Phi b).Nonempty) (hclosed : ∀ b, IsClosed (Phi b))
    (hlsc : ∀ U : Set K, IsOpen U → IsOpen {b | (Phi b ∩ U).Nonempty}) :
    ∃ v : B → K, Continuous v ∧ ∀ b, v b ∈ Phi b := by
  classical
  have hhemi := lowerHemicontinuous_iff_isOpen_inter_nonempty.mpr hlsc
  let ε : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hε (n : ℕ) : 0 < ε n := pow_pos (by norm_num) n
  let Stage (n : ℕ) := {a : LocallyConstant B K //
    ∀ b, ∃ k ∈ Phi b, dist (a b) k < ε n}
  obtain ⟨a₀, ha₀⟩ := initial_approximation Phi hne hhemi (hε 0)
  have next (n : ℕ) (a : Stage n) :
      ∃ a' : Stage (n + 1), ∀ b, dist (a.val b) (a'.val b) ≤ ε n := by
    obtain ⟨a', ha', hstep⟩ := refine_approximation Phi hhemi a.val (hε (n + 1)) a.property
    exact ⟨⟨a', ha'⟩, hstep⟩
  let step (n : ℕ) (a : Stage n) : Stage (n + 1) := (next n a).choose
  let a : (n : ℕ) → Stage n := fun n =>
    Nat.rec (motive := Stage) ⟨a₀, ha₀⟩ (fun n a => step n a) n
  have hstep (n : ℕ) (b : B) : dist ((a n).val b) ((a (n + 1)).val b) ≤ ε n :=
    (next n (a n)).choose_spec b
  let f : ℕ → BoundedContinuousFunction B K := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨(a n).val, (a n).val.continuous⟩
  have hf (n : ℕ) : dist (f n) (f (n + 1)) ≤ 1 * (1 / 2 : ℝ) ^ n := by
    apply (BoundedContinuousFunction.dist_le (by positivity)).mpr
    intro b
    simpa only [f, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
      one_mul] using hstep n b
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 2 : ℝ) 1 (by norm_num) hf)
  have htail (n : ℕ) : dist (f n) v ≤ 2 * ε n := by
    have := dist_le_of_le_geometric_of_tendsto (1 / 2 : ℝ) 1
      (by norm_num : (1 / 2 : ℝ) < 1) hf hv n
    convert this using 1
    dsimp [ε]
    ring
  refine ⟨v, v.continuous, fun b => ?_⟩
  apply (hclosed b).closure_eq ▸ Metric.mem_closure_iff.mpr ?_
  intro η hη
  have hzero : Tendsto (fun n => 3 * ε n) atTop (𝓝 (0 : ℝ)) := by
    simpa [ε] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 3
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hzero).2 η hη).exists
  obtain ⟨k, hk, hdist⟩ := (a n).property b
  refine ⟨k, hk, lt_of_le_of_lt (dist_triangle (v b) ((a n).val b) k) ?_⟩
  have hb : dist (v b) ((a n).val b) ≤ 2 * ε n := by
    simpa only [f, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
      dist_comm] using (BoundedContinuousFunction.dist_coe_le_dist b).trans (htail n)
  linarith

/-- A continuous selection can pass through any prescribed point of any fiber.
Only that fiber is replaced by a singleton before applying the full theorem. -/
theorem exists_continuous_selection_through [CompleteSpace K] (Phi : B → Set K)
    (hne : ∀ b, (Phi b).Nonempty) (hclosed : ∀ b, IsClosed (Phi b))
    (hlsc : ∀ U : Set K, IsOpen U → IsOpen {b | (Phi b ∩ U).Nonempty})
    (b₀ : B) (k₀ : K) (hk₀ : k₀ ∈ Phi b₀) :
    ∃ v : B → K, Continuous v ∧ (∀ b, v b ∈ Phi b) ∧ v b₀ = k₀ := by
  classical
  let Psi : B → Set K := fun b => if b = b₀ then {k₀} else Phi b
  have hne' (b : B) : (Psi b).Nonempty := by
    by_cases hb : b = b₀ <;> simp [Psi, hb, hne b]
  have hclosed' (b : B) : IsClosed (Psi b) := by
    by_cases hb : b = b₀ <;> simp [Psi, hb, hclosed b]
  have hlsc' (U : Set K) (hU : IsOpen U) : IsOpen {b | (Psi b ∩ U).Nonempty} := by
    by_cases hk : k₀ ∈ U
    · have heq : {b | (Psi b ∩ U).Nonempty} = {b | (Phi b ∩ U).Nonempty} := by
        ext b
        by_cases hb : b = b₀
        · subst b
          exact iff_of_true (by simpa [Psi] using hk) ⟨k₀, hk₀, hk⟩
        · simp [Psi, hb]
      rw [heq]
      exact hlsc U hU
    · have heq : {b | (Psi b ∩ U).Nonempty} =
          {b | (Phi b ∩ U).Nonempty} \ {b₀} := by
        ext b
        by_cases hb : b = b₀
        · subst b
          simp [Psi, hk]
        · simp [Psi, hb]
      rw [heq]
      exact (hlsc U hU).sdiff isClosed_singleton
  obtain ⟨v, hv, hmem⟩ := exists_continuous_selection Psi hne' hclosed' hlsc'
  refine ⟨v, hv, fun b => ?_, ?_⟩
  · have := hmem b
    by_cases hb : b = b₀
    · subst b
      have heq : v b₀ = k₀ := by simpa [Psi] using this
      exact heq.symm ▸ hk₀
    · simpa [Psi, hb] using this
  · simpa [Psi] using hmem b₀

end D5.S3.Topology.Selection.CompactZeroDimensional
