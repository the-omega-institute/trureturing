/- GID: D5/S3/Topology/Selection/Measurable
   generality: G
   mirror-B: D5/B/S3/Topology/Selection/Measurable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed-valued weak-measurable multifunctions admit measurable selectors -/

/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Tactic

/-!
# Measurable selection and sections of compact metric quotients

The least-index approximation and measurable-limit proof is adapted from
LeanPool/lean-pool, commit 7d5e94f7172d47c78cac7f23c0dd01cef1665e42,
LeanPool/BicausalOT/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean.
Copyright (c) 2026 KT. Wu. Released under the Apache 2.0 license.
Original source SHA256: a7f86e5daa9a7a200064e77f77a0e7d1f2dd2d99314b80ee5456b8892d7fb2d7.
The compact quotient application uses sigma-compact open sets to verify
weak measurability of the inverse-image multifunction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Topology.Selection.Measurable

open Metric Set Filter Topology TopologicalSpace

namespace Approximation



/-- The least `n : ℕ` satisfying `p`, with classical decidability baked in (so that it
can be used in `noncomputable` constructions without carrying instances around). -/
private noncomputable def firstIdx (p : ℕ → Prop) (h : ∃ n, p n) : ℕ :=
  @Nat.find p (Classical.decPred p) h

private theorem firstIdx_spec {p : ℕ → Prop} (h : ∃ n, p n) : p (firstIdx p h) := by
  let := Classical.decPred p
  exact Nat.find_spec h

private theorem firstIdx_eq_iff {p : ℕ → Prop} (h : ∃ n, p n) {k : ℕ} :
    firstIdx p h = k ↔ p k ∧ ∀ j < k, ¬p j := by
  let := Classical.decPred p
  exact Nat.find_eq_iff h

variable {α : Type*} [MeasurableSpace α]

/-- Taking the least index satisfying a jointly measurable family of predicates is a
measurable operation into `ℕ`. -/
private theorem measurable_firstIdx {p : α → ℕ → Prop} (hex : ∀ a, ∃ n, p a n)
    (hm : ∀ k, MeasurableSet {a | p a k}) :
    Measurable fun a => firstIdx (p a) (hex a) := by
  refine measurable_to_countable' fun k => ?_
  have hset : (fun a => firstIdx (p a) (hex a)) ⁻¹' {k} =
      {a | p a k} ∩ ⋂ (j : ℕ) (_ : j < k), {a | p a j}ᶜ := by
    ext a
    simp only [mem_preimage, mem_singleton_iff, firstIdx_eq_iff, mem_inter_iff,
      mem_ofPred_eq, mem_iInter, mem_compl_iff]
  rw [hset]
  exact (hm k).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hm j).compl)

/-! ### The approximation scheme

Throughout, `u : ℕ → Y` is a dense sequence and `Φ : α → Set Y` a multifunction with
`{a | (Φ a ∩ U).Nonempty}` measurable for every open `U`. -/

variable {Y : Type*} [MetricSpace Y] {Φ : α → Set Y} {u : ℕ → Y}

omit [MeasurableSpace α] in
/-- Base step: some `u k` comes within distance `1` of the nonempty set `Φ a`. -/
private theorem base_exists (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty) (a : α) :
    ∃ k, (Φ a ∩ ball (u k) 1).Nonempty := by
  obtain ⟨y, hy⟩ := hne a
  obtain ⟨k, hk⟩ := hu.exists_dist_lt y one_pos
  exact ⟨k, y, hy, mem_ball.mpr hk⟩

/-- The initial approximate selector: least `k` with `Φ a ∩ ball (u k) 1` nonempty. -/
private noncomputable def baseFun (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty) : α → ℕ :=
  fun a => firstIdx _ (base_exists hu hne a)

omit [MeasurableSpace α] in
private theorem baseFun_spec (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty) (a : α) :
    (Φ a ∩ ball (u (baseFun hu hne a)) 1).Nonempty :=
  firstIdx_spec (base_exists hu hne a)

private theorem baseFun_measurable (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    Measurable (baseFun hu hne) :=
  measurable_firstIdx (base_exists hu hne) fun _ => hΦ _ isOpen_ball

omit [MeasurableSpace α] in
/-- Refinement step, existence: if `Φ a` meets `ball (u (g a)) r`, then by density some
`u k` with `k` least comes within `r'` of a point of `Φ a ∩ ball (u (g a)) r`. -/
private theorem step_exists (hu : DenseRange u) {g : α → ℕ} {r : ℝ}
    (hg : ∀ a, (Φ a ∩ ball (u (g a)) r).Nonempty) {r' : ℝ} (hr' : 0 < r') (a : α) :
    ∃ k, (Φ a ∩ (ball (u k) r' ∩ ball (u (g a)) r)).Nonempty := by
  obtain ⟨y, hyΦ, hyb⟩ := hg a
  obtain ⟨k, hk⟩ := hu.exists_dist_lt y hr'
  exact ⟨k, y, hyΦ, mem_ball.mpr hk, hyb⟩

/-- Refinement step, measurability of the test sets.  This is the key point of the
whole formalization: since the previous selector `g` is countably valued, the set
splits over the fibers `{g = j}`, and on each fiber the test set is cut out by a
*fixed* open set `ball (u k) r' ∩ ball (u j) r`, so the hypothesis `hΦ` applies. -/
private theorem step_measurableSet
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    {g : α → ℕ} (hgm : Measurable g) (r r' : ℝ) (k : ℕ) :
    MeasurableSet {a | (Φ a ∩ (ball (u k) r' ∩ ball (u (g a)) r)).Nonempty} := by
  have hset : {a | (Φ a ∩ (ball (u k) r' ∩ ball (u (g a)) r)).Nonempty} =
      ⋃ j : ℕ, {a | g a = j} ∩ {a | (Φ a ∩ (ball (u k) r' ∩ ball (u j) r)).Nonempty} := by
    ext a
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · exact fun h => ⟨g a, rfl, h⟩
    · rintro ⟨j, rfl, h⟩
      exact h
  rw [hset]
  exact MeasurableSet.iUnion fun j =>
    (hgm (measurableSet_singleton j)).inter (hΦ _ (isOpen_ball.inter isOpen_ball))

/-- The refinement step: the least index `k` such that `Φ a` meets
`ball (u k) r' ∩ ball (u (g a)) r`. -/
private noncomputable def stepFun (hu : DenseRange u) {g : α → ℕ} {r : ℝ}
    (hg : ∀ a, (Φ a ∩ ball (u (g a)) r).Nonempty) {r' : ℝ} (hr' : 0 < r') : α → ℕ :=
  fun a => firstIdx _ (step_exists hu hg hr' a)

omit [MeasurableSpace α] in
private theorem stepFun_spec (hu : DenseRange u) {g : α → ℕ} {r : ℝ}
    (hg : ∀ a, (Φ a ∩ ball (u (g a)) r).Nonempty) {r' : ℝ} (hr' : 0 < r') (a : α) :
    (Φ a ∩ (ball (u (stepFun hu hg hr' a)) r' ∩ ball (u (g a)) r)).Nonempty :=
  firstIdx_spec (step_exists hu hg hr' a)

private theorem stepFun_measurable (hu : DenseRange u)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    {g : α → ℕ} {r : ℝ} (hg : ∀ a, (Φ a ∩ ball (u (g a)) r).Nonempty)
    {r' : ℝ} (hr' : 0 < r') (hgm : Measurable g) :
    Measurable (stepFun hu hg hr') :=
  measurable_firstIdx (step_exists hu hg hr') fun k => step_measurableSet hΦ hgm r r' k

/-- The full approximation scheme: at stage `n`, a measurable, countably-`u`-valued
selector index `gₙ : α → ℕ` such that `Φ a` meets `ball (u (gₙ a)) ((1/2)^n)`. -/
private noncomputable def approx (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    (n : ℕ) →
      {g : α → ℕ // Measurable g ∧ ∀ a, (Φ a ∩ ball (u (g a)) ((1 / 2 : ℝ) ^ n)).Nonempty}
  | 0 =>
    ⟨baseFun hu hne, baseFun_measurable hu hne hΦ, fun a => by
      simpa using baseFun_spec hu hne a⟩
  | n + 1 =>
    ⟨stepFun hu (approx hu hne hΦ n).2.2 (pow_pos one_half_pos (n + 1)),
      stepFun_measurable hu hΦ (approx hu hne hΦ n).2.2 (pow_pos one_half_pos (n + 1))
        (approx hu hne hΦ n).2.1,
      fun a =>
        Exists.imp (fun _ hy => ⟨hy.1, hy.2.1⟩)
          (stepFun_spec hu (approx hu hne hΦ n).2.2 (pow_pos one_half_pos (n + 1)) a)⟩

/-- Successive stages of the scheme select points close both to `Φ a` and to the
previous stage. -/
private theorem approx_succ_spec (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    (n : ℕ) (a : α) :
    (Φ a ∩ (ball (u ((approx hu hne hΦ (n + 1)).1 a)) ((1 / 2 : ℝ) ^ (n + 1)) ∩
      ball (u ((approx hu hne hΦ n).1 a)) ((1 / 2 : ℝ) ^ n))).Nonempty :=
  stepFun_spec hu (approx hu hne hΦ n).2.2 (pow_pos one_half_pos (n + 1)) a

/-- The `n`-th approximate selection `α → Y`: the dense sequence composed with the
`n`-th selector index. -/
private noncomputable def approxFun (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    (n : ℕ) (a : α) : Y :=
  u ((approx hu hne hΦ n).1 a)

private theorem approxFun_close (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    (n : ℕ) (a : α) :
    (Φ a ∩ ball (approxFun hu hne hΦ n a) ((1 / 2 : ℝ) ^ n)).Nonempty :=
  (approx hu hne hΦ n).2.2 a

private theorem approxFun_dist_succ (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    (n : ℕ) (a : α) :
    dist (approxFun hu hne hΦ n a) (approxFun hu hne hΦ (n + 1) a) ≤
      (3 / 2 : ℝ) * (1 / 2) ^ n := by
  obtain ⟨y, hyΦ, hy1, hy2⟩ := approx_succ_spec hu hne hΦ n a
  calc dist (approxFun hu hne hΦ n a) (approxFun hu hne hΦ (n + 1) a) ≤
      dist y (approxFun hu hne hΦ n a) + dist y (approxFun hu hne hΦ (n + 1) a) :=
        dist_triangle_left _ _ _
    _ ≤ (1 / 2 : ℝ) ^ n + (1 / 2) ^ (n + 1) :=
        add_le_add (mem_ball.mp hy2).le (mem_ball.mp hy1).le
    _ = (3 / 2 : ℝ) * (1 / 2) ^ n := by rw [pow_succ]; ring

private theorem approxFun_measurable [MeasurableSpace Y] (hu : DenseRange u)
    (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) (n : ℕ) :
    Measurable (approxFun hu hne hΦ n) :=
  (Measurable.of_discrete (f := u)).comp (approx hu hne hΦ n).2.1

section Limit

variable [MeasurableSpace Y] [BorelSpace Y]

/-- Main construction, given a dense sequence: the approximations form a uniformly
Cauchy sequence; the pointwise limit is a measurable selection of `Φ`. -/
private theorem exists_selection_of_denseRange [CompleteSpace Y]
    (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty) (hclosed : ∀ a, IsClosed (Φ a))
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → Y, Measurable f ∧ ∀ a, f a ∈ Φ a := by
  have hcauchy : ∀ a, CauchySeq fun n => approxFun hu hne hΦ n a := fun a =>
    cauchySeq_of_le_geometric (1 / 2) (3 / 2) (by norm_num)
      (fun n => approxFun_dist_succ hu hne hΦ n a)
  choose f hf using fun a => cauchySeq_tendsto_of_complete (hcauchy a)
  refine ⟨f, ?_, ?_⟩
  · exact measurable_of_tendsto_metrizable (fun n => approxFun_measurable hu hne hΦ n)
      (tendsto_pi_nhds.mpr hf)
  · intro a
    rw [← (hclosed a).closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have h1 : ∀ᶠ n in atTop, dist (approxFun hu hne hΦ n a) (f a) < ε / 2 := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hf a) (ε / 2) (half_pos hε)
      exact eventually_atTop.mpr ⟨N, hN⟩
    have h2 : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ^ n < ε / 2 :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually_lt_const
        (half_pos hε)
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    obtain ⟨y, hyΦ, hyb⟩ := approxFun_close hu hne hΦ n a
    refine ⟨y, hyΦ, ?_⟩
    calc dist (f a) y ≤
        dist (f a) (approxFun hu hne hΦ n a) + dist (approxFun hu hne hΦ n a) y :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 :=
          add_lt_add (by rw [dist_comm]; exact hn1) ((mem_ball'.mp hyb).trans hn2)
      _ = ε := by ring

end Limit

end Approximation

/-- **The Kuratowski–Ryll-Nardzewski measurable selection theorem** (single-selection
form): a multifunction `Φ` from a measurable space into a complete separable metric
space, with nonempty closed values, such that `{a | (Φ a ∩ U).Nonempty}` is measurable
for every open `U`, admits a Borel-measurable selection. -/
theorem exists_measurable_selection {α : Type*} [MeasurableSpace α] {Y : Type*}
    [MetricSpace Y] [SeparableSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {Φ : α → Set Y} (hne : ∀ a, (Φ a).Nonempty)
    (hclosed : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → Y, Measurable f ∧ ∀ a, f a ∈ Φ a := by
  rcases isEmpty_or_nonempty α with hα | hα
  · have := hα
    exact ⟨fun a => (hne a).some, measurable_of_empty _, fun a => (hne a).some_mem⟩
  · obtain ⟨a₀⟩ := hα
    have : Nonempty Y := ⟨(hne a₀).some⟩
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq Y
    exact Approximation.exists_selection_of_denseRange hu hne hclosed hmeas

/-- A continuous surjection from a compact metric space to a Hausdorff
Borel space has a measurable right inverse. Empty carriers are allowed. -/
theorem exists_measurable_right_inverse {K : Type*} [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] {L : Type*} [TopologicalSpace L] [T2Space L]
    [MeasurableSpace L] [BorelSpace L] (p : K → L) (hp : Continuous p)
    (hsurj : Function.Surjective p) :
    ∃ q : L → K, Measurable q ∧ Function.RightInverse q p := by
  let Φ : L → Set K := fun y => p ⁻¹' {y}
  have hne : ∀ y, (Φ y).Nonempty := fun y => by
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, hx⟩
  have hclosed : ∀ y, IsClosed (Φ y) := fun y => isClosed_singleton.preimage hp
  have hmeas : ∀ U : Set K, IsOpen U →
      MeasurableSet {y | (Φ y ∩ U).Nonempty} := by
    intro U hU
    haveI : LocallyCompactSpace U := hU.locallyCompactSpace
    have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
    obtain ⟨C, hC, hcover⟩ := IsSigmaCompact.image hp hσ
    have heq : {y | (Φ y ∩ U).Nonempty} = p '' U := by
      ext y
      constructor
      · rintro ⟨x, hx, hxU⟩
        exact ⟨x, hxU, hx⟩
      · rintro ⟨x, hxU, hxy⟩
        exact ⟨x, hxy, hxU⟩
    rw [heq, ← hcover]
    exact MeasurableSet.iUnion fun n => (hC n).isClosed.measurableSet
  obtain ⟨q, hq, hmem⟩ := exists_measurable_selection hne hclosed hmeas
  exact ⟨q, hq, hmem⟩

end D5.S3.Topology.Selection.Measurable
