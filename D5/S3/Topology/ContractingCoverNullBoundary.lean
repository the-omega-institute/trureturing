/- GID: D5/S3/Topology/ContractingCoverNullBoundary
   generality: G
   mirror-B: D5/B/S3/Topology/ContractingCoverNullBoundary
   mirror-E: none(waiver:unbounded-metric-measure-inference)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Measure.Typeclasses.Finite]
   utility: none
   digest: An interior cylinder in a finite contracting open self-cover forces strict loss of boundary mass. -/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Maps.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Positivity

/-! Finite varying-word covers, an interior cylinder, and strict loss of boundary mass. -/

open scoped Topology BigOperators

namespace D5.S3.Topology.ContractingCoverNullBoundary

open Set Metric Filter MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A cylinder records a varying word of branches, with its first letter outermost. -/
def cylinderMap {X I : Type*} (f : I → X → X) :
    (N : ℕ) → (Fin N → I) → X → X
  | 0, _ => id
  | N + 1, w => f (w 0) ∘ cylinderMap f N (Fin.tail w)

private theorem cylinder_lipschitz {X I : Type*} [MetricSpace X]
    {q : NNReal} (f : I → X → X) (hlip : ∀ i, LipschitzWith q (f i))
    (N : ℕ) (w : Fin N → I) : LipschitzWith (q ^ N) (cylinderMap f N w) := by
  induction N with
  | zero => simpa [cylinderMap] using (LipschitzWith.id : LipschitzWith 1 (id : X → X))
  | succ N ih =>
    simpa [cylinderMap, pow_succ, mul_comm] using (hlip (w 0)).comp (ih (Fin.tail w))

private theorem cylinder_open {X I : Type*} [TopologicalSpace X]
    (f : I → X → X) (hopen : ∀ i, IsOpenMap (f i))
    (N : ℕ) (w : Fin N → I) : IsOpenMap (cylinderMap f N w) := by
  induction N with
  | zero => exact (Homeomorph.refl X).isOpenMap
  | succ N ih => exact (hopen (w 0)).comp (ih (Fin.tail w))

private theorem cylinder_mapsTo {X I : Type*} {K : Set X}
    (f : I → X → X) (hmap : ∀ i, MapsTo (f i) K K)
    (N : ℕ) (w : Fin N → I) : MapsTo (cylinderMap f N w) K K := by
  induction N with
  | zero => exact fun _ hx => hx
  | succ N ih => exact (hmap (w 0)).comp (ih (Fin.tail w))

private theorem cylinder_preimage {X I : Type*} {K : Set X}
    (f : I → X → X) (hcover : (⋃ i, f i '' K) = K)
    (N : ℕ) (x : X) (hx : x ∈ K) :
    ∃ w : Fin N → I, ∃ y ∈ K, cylinderMap f N w y = x := by
  induction N generalizing x with
  | zero => exact ⟨Fin.elim0, x, hx, rfl⟩
  | succ N ih =>
    rw [← hcover] at hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    obtain ⟨w, t, ht, he⟩ := ih y hy
    exact ⟨Fin.cons i w, t, ht, by simp [cylinderMap, he]⟩

/-- One whole cylinder lies in the interior, and deleting it still covers the frontier
by images of the frontier. No forward invariance of the frontier is asserted. -/
theorem exists_interior_cylinder_frontier_cover
    {X I : Type*} [MetricSpace X] {K : Set X}
    (hK : IsCompact K) (hint : (interior K).Nonempty)
    {q : NNReal} (hq : q < 1) (f : I → X → X)
    (hlip : ∀ i, LipschitzWith q (f i)) (hopen : ∀ i, IsOpenMap (f i))
    (hcover : (⋃ i, f i '' K) = K) :
    ∃ N : ℕ, 0 < N ∧ ∃ w₀ : Fin N → I,
      cylinderMap f N w₀ '' K ⊆ interior K ∧
      frontier K ⊆ ⋃ w : {w : Fin N → I // w ≠ w₀},
        cylinderMap f N w.val '' frontier K := by
  have hmap : ∀ i, MapsTo (f i) K K := by
    intro i x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, x, hx, rfl⟩
  obtain ⟨x, hx⟩ := hint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hlim : Tendsto (fun N : ℕ => (q : ℝ) ^ N * diam K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one q.coe_nonneg
      (show (q : ℝ) < 1 from hq)).mul_const (diam K)
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  let N := n + 1
  have hsmall : (q : ℝ) ^ N * diam K < ε := hn N (Nat.le_succ n)
  obtain ⟨w₀, y, hy, he⟩ := cylinder_preimage f hcover N x (interior_subset hx)
  have hinside : cylinderMap f N w₀ '' K ⊆ interior K := by
    rintro _ ⟨t, ht, rfl⟩
    apply hball
    change dist (cylinderMap f N w₀ t) x < ε
    rw [← he]
    exact ((cylinder_lipschitz f hlip N w₀).dist_le_mul t y |>.trans
      (mul_le_mul_of_nonneg_left (dist_le_diam_of_mem hK.isBounded ht hy)
        (by positivity))).trans_lt hsmall
  refine ⟨N, Nat.succ_pos n, w₀, hinside, ?_⟩
  intro b hb
  have hbK := hK.isClosed.frontier_subset hb
  have hbnot : b ∉ interior K := by
    exact hb.2
  obtain ⟨w, t, ht, he⟩ := cylinder_preimage f hcover N b hbK
  have htB : t ∈ frontier K := by
    rw [hK.isClosed.frontier_eq]
    refine ⟨ht, ?_⟩
    intro hti
    exact hbnot (he ▸ (cylinder_open f hopen N w).mapsTo_interior
      (cylinder_mapsTo f hmap N w) hti)
  have hw : w ≠ w₀ := by
    intro h
    subst w
    exact hbnot (hinside ⟨t, ht, he⟩)
  exact mem_iUnion.mpr ⟨⟨w, hw⟩, t, htB, he⟩

private theorem cylinder_measure {X I : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) {q : NNReal} (f : I → X → X)
    (hlip : ∀ i, LipschitzWith q (f i)) (a : I → NNReal)
    (hscale : ∀ i (S : Set X), IsCompact S → μ (f i '' S) = (a i : ENNReal) * μ S)
    (N : ℕ) (w : Fin N → I) (S : Set X) (hS : IsCompact S) :
    μ (cylinderMap f N w '' S) = ((∏ j, a (w j) : NNReal) : ENNReal) * μ S := by
  induction N with
  | zero => simp [cylinderMap]
  | succ N ih =>
    rw [cylinderMap, image_comp, hscale _ _ (hS.image
      (cylinder_lipschitz f hlip N (Fin.tail w)).continuous), ih (Fin.tail w),
      Fin.prod_univ_succ]
    simp only [ENNReal.coe_mul, mul_assoc, Fin.tail]

/-- Positive similarity weights of total one and finite mass on compacts turn the
omitted interior cylinder into strict boundary-mass loss. -/
theorem measure_frontier_eq_zero_of_contracting_cover
    {X I : Type*} [MetricSpace X] [MeasurableSpace X] [Fintype I]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {K : Set X} (hK : IsCompact K) (hint : (interior K).Nonempty)
    {q : NNReal} (hq : q < 1) (f : I → X → X)
    (hlip : ∀ i, LipschitzWith q (f i)) (hopen : ∀ i, IsOpenMap (f i))
    (hcover : (⋃ i, f i '' K) = K)
    (a : I → NNReal) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = 1)
    (hscale : ∀ i (S : Set X), IsCompact S → μ (f i '' S) = (a i : ENNReal) * μ S) :
    μ (frontier K) = 0 := by
  classical
  obtain ⟨N, _, w₀, _, hBcover⟩ :=
    exists_interior_cylinder_frontier_cover hK hint hq f hlip hopen hcover
  let A : (Fin N → I) → NNReal := fun w => ∏ j, a (w j)
  have htotal : ∑ w, A w = 1 := by
    simpa [A, hsum] using (Fintype.prod_sum (fun (_ : Fin N) i => a i)).symm
  have hApos : 0 < A w₀ := Finset.prod_pos (fun j _ => hpos (w₀ j))
  let c : NNReal := ∑ w : {w : Fin N → I // w ≠ w₀}, A w.val
  have hsplit : c + A w₀ = 1 := by
    have he := Fintype.sum_subtype_add_sum_subtype (fun w : Fin N → I => w ≠ w₀) A
    have heq : (∑ w : {w : Fin N → I // ¬ w ≠ w₀}, A w.val) = A w₀ := by
      apply Finset.sum_eq_single (s := Finset.univ)
        (f := fun w : {w : Fin N → I // ¬ w ≠ w₀} => A w.val) ⟨w₀, by simp⟩
      · intro w _ hw
        exact False.elim (hw (Subtype.ext (not_ne_iff.mp w.property)))
      · simp
    rw [heq, htotal] at he
    exact he
  have hc : c < 1 := by
    calc
      c < c + A w₀ := lt_add_of_pos_right c hApos
      _ = 1 := hsplit
  have hBc : IsCompact (frontier K) :=
    hK.of_isClosed_subset isClosed_frontier hK.isClosed.frontier_subset
  have hmass : μ (frontier K) ≤ (c : ENNReal) * μ (frontier K) := by
    calc
      μ (frontier K) ≤ μ (⋃ w : {w : Fin N → I // w ≠ w₀},
          cylinderMap f N w.val '' frontier K) := measure_mono hBcover
      _ ≤ ∑ w : {w : Fin N → I // w ≠ w₀},
          μ (cylinderMap f N w.val '' frontier K) := measure_iUnion_fintype_le μ _
      _ = (c : ENNReal) * μ (frontier K) := by
        simp only [cylinder_measure μ f hlip a hscale N _ _ hBc]
        simp [c, A, Finset.sum_mul]
  by_contra hnonzero
  have hstrict := ENNReal.mul_lt_mul_left hnonzero hBc.measure_ne_top
    (show (c : ENNReal) < 1 from ENNReal.coe_lt_coe.mpr hc)
  exact (not_lt_of_ge hmass) (by simpa only [one_mul] using hstrict)

end D5.S3.Topology.ContractingCoverNullBoundary
