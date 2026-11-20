/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q8OrderedFiberCapacityCertificate
   generality: I
   mirror-B: none(waiver:isolated-verification)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Ordered fibre projections exclude a closed neighborhood of size 107 for 36 vertices with large halves. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8FourFiberCapacityCertificate

/-! A table on two or more axes is recovered by joining two child projections
along their common marginal. The certificate also checks every other child
projection against the preceding level. -/

set_option autoImplicit false

open private fastCost glue joinPair joinPair_complete dropAxis_spec singles singles_complete from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8FourFiberCapacityCertificate

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8OrderedFiberCapacityCertificate

open Q8FourFiberCapacityCertificate (dropAxis neighborhoodCost ProjectionConstraints)

private def joinPairWhere (d cap : ℕ) (left right : List ℕ)
    (keep : List ℕ → Bool) : List (List ℕ) :=
  let width := 2 ^ d
  let base := dropAxis d d left
  if base = dropAxis d d right then
    (glue (2 ^ (8 - (d + 2))) base (left.drop width) (right.drop width)).filterMap
      fun (a, b, c, e) =>
        let counts := a ++ b ++ c ++ e
        if keep counts && decide (fastCost (d + 2) counts ≤ cap) then some counts else none
  else []

/-- At two axes, the 1-marginals are ordered precisely when the second count
does not exceed the third. At higher dimensions, inherit this test on all
two-axis projections. -/
def OrderedProjections : ℕ → List ℕ → Prop
  | 0, _ | 1, _ => True
  | 2, counts => counts[1]! ≤ counts[2]!
  | d + 3, counts =>
    ∀ axis : Fin (d + 3), OrderedProjections (d + 2) (dropAxis (d + 2) axis counts)

-- A key comparison is a cheap prefilter. Collisions can only retain more
-- tables, and the final containment check still compares whole tables.
private def key (counts : List ℕ) : ℕ :=
  counts.foldl (fun acc x => 256 * acc + x) 0

private def keepProjection (d : ℕ) (keys : List ℕ) (counts : List ℕ) : Bool :=
  (d != 0 || decide (counts[1]! ≤ counts[2]!)) &&
    (List.range d).all (fun axis => keys.contains (key (dropAxis (d + 1) axis counts)))

private def sharedGroup (d : ℕ) (previous : List (List ℕ)) (base : List ℕ) :
    List (List ℕ) :=
  previous.filter (fun t => dropAxis d d t == base)

private def checkGroup (d cap : ℕ) (previous next : List (List ℕ)) (base : List ℕ) : Bool :=
  let group := sharedGroup d previous base
  let keys := previous.map key
  group.all fun left => group.all fun right =>
    (joinPairWhere d cap left right (keepProjection d keys)).all next.contains

private theorem mem_joinPairWhere {d cap : ℕ} {left right counts : List ℕ}
    {keep : List ℕ → Bool} (h : counts ∈ joinPair d cap left right)
    (hk : keep counts = true) :
    counts ∈ joinPairWhere d cap left right keep := by
  by_cases hbase : dropAxis d d left = dropAxis d d right
  · simp only [joinPair, hbase, ite_true] at h
    simp only [joinPairWhere, hbase, ite_true]
    obtain ⟨⟨a, b, c, e⟩, hm, he⟩ := List.mem_filterMap.mp h
    dsimp only at he
    split at he
    · cases he
      exact List.mem_filterMap.mpr ⟨(a, b, c, e), hm, by simp_all⟩
    · simp at he
  · simp [joinPair, hbase] at h

private def checkGroups (d cap : ℕ) (previous next bases : List (List ℕ)) : Bool :=
  bases.all (checkGroup d cap previous next)

private theorem checkedStep {d cap : ℕ} {previous next bases : List (List ℕ)}
    (hbase : ∀ t ∈ previous, dropAxis d d t ∈ bases)
    (hcheck : checkGroups d cap previous next bases = true)
    (counts : List ℕ) (hlen : counts.length = 2 ^ (d + 2))
    (hcap : ∀ x ∈ counts, x ≤ 2 ^ (8 - (d + 2)))
    (hcost : neighborhoodCost (d + 2) counts ≤ cap)
    (horder : OrderedProjections (d + 2) counts)
    (hchild : ∀ axis : Fin (d + 2), dropAxis (d + 1) axis counts ∈ previous) :
    counts ∈ next := by
  let left := dropAxis (d + 1) (d + 1) counts
  let right := dropAxis (d + 1) d counts
  let base := dropAxis d d left
  have hl : left ∈ previous := hchild ⟨d + 1, by omega⟩
  have hr : right ∈ previous := hchild ⟨d, by omega⟩
  have hj : counts ∈ joinPair d cap left right := joinPair_complete d cap counts hlen hcost hcap
  have heq : dropAxis d d right = base := by
    by_contra hn
    change dropAxis d d right ≠ dropAxis d d left at hn
    simp only [joinPair, ite_eq_right (Ne.symm hn), List.not_mem_nil] at hj
  have hk : keepProjection d (previous.map key) counts = true := by
    unfold keepProjection
    refine Bool.and_eq_true_iff.mpr ⟨?_, List.all_eq_true.mpr ?_⟩
    · cases d with
      | zero => simpa [OrderedProjections] using horder
      | succ d => rfl
    · intro axis ha
      exact List.contains_iff_mem.mpr (List.mem_map_of_mem
        (hchild ⟨axis, by have := List.mem_range.mp ha; omega⟩))
  have hgroup := List.all_eq_true.mp hcheck base (hbase left hl)
  have hleft : left ∈ sharedGroup d previous base := by simp [sharedGroup, hl, base]
  have hright : right ∈ sharedGroup d previous base := by simp [sharedGroup, hr, heq]
  exact List.contains_iff_mem.mp
    (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
      hgroup left hleft) right hright) counts (mem_joinPairWhere hj hk))

private theorem complete_of_step {cap : ℕ} (d : ℕ) (hd : d + 2 ≤ 8)
    (previous next : List (List ℕ))
    (hprev : ∀ counts : List ℕ, counts.length = 2 ^ (d + 1) → counts.sum = 36 →
      (∀ x ∈ counts, x ≤ 2 ^ (8 - (d + 1))) →
      ProjectionConstraints 36 cap (d + 1) counts → OrderedProjections (d + 1) counts →
      counts ∈ previous)
    (hstep : ∀ counts : List ℕ, counts.length = 2 ^ (d + 2) →
      (∀ x ∈ counts, x ≤ 2 ^ (8 - (d + 2))) →
      neighborhoodCost (d + 2) counts ≤ cap → OrderedProjections (d + 2) counts →
      (∀ axis : Fin (d + 2), dropAxis (d + 1) axis counts ∈ previous) → counts ∈ next)
    (counts : List ℕ) (hlen : counts.length = 2 ^ (d + 2)) (hsum : counts.sum = 36)
    (hcap : ∀ x ∈ counts, x ≤ 2 ^ (8 - (d + 2)))
    (hproj : ProjectionConstraints 36 cap (d + 2) counts)
    (horder : OrderedProjections (d + 2) counts) : counts ∈ next := by
  apply hstep counts hlen hcap hproj.1 horder
  intro axis
  obtain ⟨hl, hs, hc⟩ := dropAxis_spec (d + 1) axis counts hlen
  have hpow : 2 ^ (8 - (d + 1)) = 2 ^ (8 - (d + 2)) + 2 ^ (8 - (d + 2)) := by
    rw [show 8 - (d + 1) = (8 - (d + 2)) + 1 by omega, pow_succ, Nat.mul_two]
  refine hprev _ hl (hs.trans hsum) (hpow.symm ▸ hc _ hcap) (hproj.2.2 axis) ?_
  cases d with
  | zero => trivial
  | succ d => exact horder axis

private theorem all_cons_true {α : Type} {test : α → Bool} {a : α} {as : List α}
    (ha : test a = true) (has : as.all test = true) : (a :: as).all test = true := by
  rw [List.all_cons, ha, has]
  rfl

private theorem covers_bases {d : ℕ} {previous bases : List (List ℕ)}
    (h : (previous.map (dropAxis d d)).all bases.contains = true) :
    ∀ t ∈ previous, dropAxis d d t ∈ bases :=
  fun _ ht => List.contains_iff_mem.mp (List.all_eq_true.mp h _ (List.mem_map_of_mem ht))

-- Completeness needs containment at each level. For each common marginal,
-- the kernel checks joins one left projection at a time.
local macro "verify_group" d:num previous:ident base:ident members:term : tactic =>
  `(tactic| (
    have hgroup : sharedGroup $d $previous $base = $members := by decide +kernel
    unfold checkGroup
    rw [hgroup]
    repeat
      refine all_cons_true ?_ ?_
      · decide +kernel
    rfl))

private abbrev level1 := singles 36 107

private def level2 : List (List ℕ) := [
    [7, 12, 12, 5], [7, 12, 14, 3], [7, 12, 15, 2], [10, 12, 12, 2], [12, 7, 7, 10],
    [12, 7, 10, 7], [12, 7, 12, 5], [12, 10, 12, 2], [14, 7, 7, 8], [14, 7, 8, 7], [15, 7, 7, 7],
    [16, 3, 3, 14], [16, 3, 5, 12], [16, 3, 7, 10], [16, 5, 7, 8], [16, 5, 8, 7], [16, 6, 7, 7],
    [16, 7, 7, 6], [16, 7, 8, 5], [17, 4, 7, 8], [17, 4, 8, 7], [17, 5, 7, 7], [17, 6, 6, 7],
    [17, 6, 7, 6], [17, 7, 7, 5], [17, 7, 8, 4], [18, 3, 7, 8], [18, 4, 7, 7], [18, 5, 6, 7],
    [18, 5, 7, 6], [18, 6, 6, 6], [18, 6, 7, 5], [18, 7, 7, 4], [19, 4, 5, 8], [19, 4, 6, 7],
    [19, 5, 5, 7], [19, 5, 6, 6], [19, 6, 6, 5], [20, 4, 5, 7], [20, 5, 5, 6],
    [21, 4, 4, 7]]

private def base2_0 : List ℕ := [36]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check2_0 :
    checkGroup 0 107 level1 level2 base2_0 = true := by
  verify_group 0 level1 base2_0 [
    [25, 11], [24, 12], [23, 13], [22, 14], [21, 15],
    [19, 17]]

private def bases2 : List (List ℕ) := [base2_0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
-- Check that the listed common marginals cover the preceding level.
private theorem covers2 :
    (level1.map (dropAxis 0 0)).all (bases2.contains) = true := by
  decide +kernel

private theorem check2 :
    checkGroups 0 107 level1 level2 bases2 = true := by
  simp only [checkGroups, bases2, List.all_cons, List.all_nil,
    check2_0, Bool.and_self]

private def level3 : List (List ℕ) := [
    [2, 8, 10, 2, 10, 2, 2, 0], [6, 1, 6, 6, 6, 6, 1, 4], [6, 1, 6, 6, 6, 6, 4, 1],
    [6, 1, 6, 6, 8, 6, 2, 1], [6, 1, 6, 6, 9, 6, 1, 1], [6, 1, 6, 6, 10, 4, 2, 1],
    [6, 6, 1, 6, 6, 1, 6, 4], [6, 6, 1, 6, 9, 1, 6, 1], [6, 6, 6, 1, 1, 6, 6, 4],
    [6, 6, 6, 1, 4, 6, 6, 1], [6, 6, 6, 1, 6, 1, 4, 6], [6, 6, 6, 1, 6, 1, 6, 4],
    [6, 6, 6, 1, 6, 4, 6, 1], [8, 6, 6, 1, 2, 6, 6, 1], [8, 6, 6, 1, 6, 1, 2, 6],
    [9, 1, 6, 6, 6, 6, 1, 1], [9, 6, 1, 6, 6, 1, 6, 1], [9, 6, 6, 1, 1, 6, 6, 1],
    [9, 6, 6, 1, 6, 1, 1, 6], [10, 2, 6, 1, 6, 4, 1, 6], [10, 4, 6, 1, 2, 6, 6, 1],
    [10, 4, 6, 1, 6, 1, 2, 6], [10, 4, 6, 1, 6, 2, 1, 6], [10, 5, 6, 1, 6, 1, 1, 6],
    [10, 6, 2, 1, 2, 1, 8, 6], [10, 6, 2, 1, 2, 1, 10, 4], [10, 6, 2, 1, 4, 1, 6, 6],
    [10, 6, 2, 1, 6, 1, 6, 4], [10, 6, 2, 4, 6, 1, 6, 1], [10, 6, 6, 0, 6, 1, 1, 6],
    [10, 6, 6, 1, 6, 1, 1, 5], [10, 6, 6, 1, 6, 1, 2, 4], [11, 3, 6, 1, 6, 1, 2, 6],
    [11, 3, 6, 1, 6, 2, 1, 6], [11, 4, 6, 1, 6, 1, 1, 6], [11, 5, 5, 1, 6, 1, 1, 6],
    [11, 5, 6, 0, 6, 1, 1, 6], [11, 5, 6, 1, 6, 1, 0, 6], [11, 5, 6, 1, 6, 1, 1, 5],
    [11, 6, 5, 1, 6, 0, 1, 6], [11, 6, 6, 0, 5, 1, 1, 6], [11, 6, 6, 0, 6, 0, 1, 6],
    [11, 6, 6, 0, 6, 1, 1, 5], [11, 6, 6, 1, 6, 1, 1, 4], [11, 6, 6, 1, 6, 1, 2, 3],
    [12, 2, 6, 1, 6, 2, 1, 6], [12, 3, 6, 1, 6, 1, 1, 6], [12, 4, 5, 1, 6, 1, 1, 6],
    [12, 4, 6, 0, 6, 1, 1, 6], [12, 4, 6, 1, 6, 1, 0, 6], [12, 4, 6, 1, 6, 1, 1, 5],
    [12, 5, 5, 0, 6, 1, 1, 6], [12, 5, 5, 1, 5, 1, 1, 6], [12, 5, 5, 1, 6, 0, 1, 6],
    [12, 5, 5, 1, 6, 1, 1, 5], [12, 5, 6, 0, 5, 1, 1, 6], [12, 5, 6, 0, 6, 0, 1, 6],
    [12, 5, 6, 0, 6, 1, 0, 6], [12, 5, 6, 0, 6, 1, 1, 5], [12, 5, 6, 1, 6, 1, 0, 5],
    [12, 5, 6, 1, 6, 1, 1, 4], [12, 6, 5, 0, 6, 0, 1, 6], [12, 6, 5, 1, 6, 0, 1, 5],
    [12, 6, 6, 0, 5, 1, 1, 5], [12, 6, 6, 0, 6, 0, 0, 6], [12, 6, 6, 0, 6, 0, 1, 5],
    [12, 6, 6, 0, 6, 1, 1, 4], [12, 6, 6, 1, 6, 1, 1, 3], [13, 3, 4, 1, 6, 1, 2, 6],
    [13, 3, 4, 1, 6, 2, 1, 6], [13, 3, 4, 2, 6, 1, 1, 6], [13, 3, 5, 1, 6, 1, 1, 6],
    [13, 3, 6, 1, 6, 1, 0, 6], [13, 4, 3, 1, 6, 1, 2, 6], [13, 4, 4, 1, 6, 1, 1, 6],
    [13, 4, 5, 0, 6, 1, 1, 6], [13, 4, 5, 1, 5, 1, 1, 6], [13, 4, 5, 1, 6, 0, 1, 6],
    [13, 4, 5, 1, 6, 1, 0, 6], [13, 4, 5, 1, 6, 1, 1, 5], [13, 4, 6, 0, 5, 1, 1, 6],
    [13, 4, 6, 0, 6, 1, 0, 6], [13, 4, 6, 1, 6, 1, 0, 5], [13, 5, 4, 1, 6, 0, 1, 6],
    [13, 5, 5, 0, 5, 1, 1, 6], [13, 5, 5, 0, 6, 0, 1, 6], [13, 5, 5, 0, 6, 1, 1, 5],
    [13, 5, 5, 1, 5, 1, 1, 5], [13, 5, 5, 1, 6, 0, 0, 6], [13, 5, 5, 1, 6, 0, 1, 5],
    [13, 5, 5, 1, 6, 1, 1, 4], [13, 5, 6, 0, 5, 1, 0, 6], [13, 5, 6, 0, 5, 1, 1, 5],
    [13, 5, 6, 0, 6, 0, 0, 6], [13, 5, 6, 0, 6, 1, 0, 5], [13, 5, 6, 1, 6, 1, 0, 4],
    [13, 6, 5, 0, 5, 0, 1, 6], [13, 6, 5, 0, 6, 0, 1, 5], [13, 6, 5, 1, 6, 0, 1, 4],
    [13, 6, 6, 0, 5, 1, 1, 4], [13, 6, 6, 0, 6, 0, 0, 5], [14, 3, 4, 1, 6, 1, 1, 6],
    [14, 3, 5, 1, 5, 1, 1, 6], [14, 3, 5, 1, 6, 1, 0, 6], [14, 4, 4, 0, 6, 1, 1, 6],
    [14, 4, 4, 1, 5, 1, 1, 6], [14, 4, 4, 1, 6, 0, 1, 6], [14, 4, 4, 1, 6, 1, 1, 5],
    [14, 4, 5, 0, 5, 1, 1, 6], [14, 4, 5, 0, 6, 1, 0, 6], [14, 4, 5, 1, 5, 1, 0, 6],
    [14, 4, 5, 1, 5, 1, 1, 5], [14, 4, 5, 1, 6, 0, 0, 6], [14, 4, 5, 1, 6, 1, 0, 5],
    [14, 4, 6, 0, 5, 1, 0, 6], [14, 5, 4, 0, 6, 0, 1, 6], [14, 5, 4, 1, 5, 0, 1, 6],
    [14, 5, 4, 1, 6, 0, 1, 5], [14, 5, 5, 0, 4, 1, 1, 6], [14, 5, 5, 0, 5, 1, 1, 5],
    [14, 5, 5, 1, 5, 1, 1, 4], [15, 3, 3, 1, 6, 1, 1, 6], [15, 3, 4, 1, 5, 1, 1, 6],
    [15, 3, 4, 1, 6, 1, 0, 6], [15, 3, 5, 1, 5, 1, 0, 6], [15, 4, 3, 1, 6, 0, 1, 6],
    [15, 4, 4, 0, 5, 1, 1, 6], [15, 4, 4, 1, 4, 1, 1, 6], [15, 4, 4, 1, 5, 0, 1, 6],
    [15, 4, 4, 1, 5, 1, 1, 5], [15, 4, 4, 1, 6, 0, 0, 6], [15, 4, 5, 0, 4, 1, 1, 6],
    [15, 4, 5, 0, 5, 1, 0, 6], [15, 4, 5, 1, 5, 1, 0, 5], [15, 5, 4, 0, 5, 0, 1, 6],
    [15, 5, 4, 1, 5, 0, 1, 5],
    [15, 5, 5, 0, 4, 1, 1, 5]]

private def base3_0 : List ℕ := [19, 17]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check3_0 :
    checkGroup 1 107 level2 level3 base3_0 = true := by
  verify_group 1 level2 base3_0 [
    [7, 12, 12, 5], [12, 7, 7, 10],
    [16, 3, 3, 14]]

private def base3_1 : List ℕ := [21, 15]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check3_1 :
    checkGroup 1 107 level2 level3 base3_1 = true := by
  verify_group 1 level2 base3_1 [
    [7, 12, 14, 3], [14, 7, 7, 8],
    [16, 3, 5, 12]]

private def base3_2 : List ℕ := [22, 14]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check3_2 :
    checkGroup 1 107 level2 level3 base3_2 = true := by
  verify_group 1 level2 base3_2 [
    [7, 12, 15, 2], [10, 12, 12, 2], [12, 7, 10, 7], [14, 7, 8, 7],
    [15, 7, 7, 7]]

private def base3_3 : List ℕ := [23, 13]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check3_3 :
    checkGroup 1 107 level2 level3 base3_3 = true := by
  verify_group 1 level2 base3_3 [
    [16, 3, 7, 10], [16, 5, 7, 8], [16, 6, 7, 7], [16, 7, 7, 6],
    [17, 6, 6, 7]]

private def base3_4 : List ℕ := [24, 12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check3_4 :
    checkGroup 1 107 level2 level3 base3_4 = true := by
  verify_group 1 level2 base3_4 [
    [12, 7, 12, 5], [12, 10, 12, 2], [16, 5, 8, 7], [16, 7, 8, 5], [17, 4, 7, 8], [17, 5, 7, 7],
    [17, 6, 7, 6], [17, 7, 7, 5], [18, 5, 6, 7], [18, 6, 6, 6], [19, 4, 5, 8],
    [19, 5, 5, 7]]

private def base3_5 : List ℕ := [25, 11]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check3_5 :
    checkGroup 1 107 level2 level3 base3_5 = true := by
  verify_group 1 level2 base3_5 [
    [17, 4, 8, 7], [17, 7, 8, 4], [18, 3, 7, 8], [18, 4, 7, 7], [18, 5, 7, 6], [18, 6, 7, 5],
    [18, 7, 7, 4], [19, 4, 6, 7], [19, 5, 6, 6], [19, 6, 6, 5], [20, 4, 5, 7], [20, 5, 5, 6],
    [21, 4, 4, 7]]

private def bases3 : List (List ℕ) := [base3_0, base3_1, base3_2, base3_3, base3_4, base3_5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
-- Check that the listed common marginals cover the preceding level.
private theorem covers3 :
    (level2.map (dropAxis 1 1)).all (bases3.contains) = true := by
  decide +kernel

private theorem check3 :
    checkGroups 1 107 level2 level3 bases3 = true := by
  simp only [checkGroups, bases3, List.all_cons, List.all_nil,
    check3_0, check3_1, check3_2, check3_3, check3_4, check3_5, Bool.and_self]

private def level4 : List (List ℕ) := [
    [1, 5, 5, 1, 5, 1, 1, 0, 1, 3, 5, 1, 5, 1, 1, 0],
    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 3, 5, 1],
    [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 1, 1, 3],
    [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 3, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 3, 5, 5, 1, 1, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 4, 5, 5, 1, 0, 1, 1, 0],
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 3, 5, 1, 1, 1, 1, 0],
    [5, 1, 1, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 1, 3],
    [5, 1, 1, 5, 1, 0, 5, 1, 4, 5, 0, 1, 5, 1, 1, 0],
    [5, 1, 1, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 1, 3],
    [5, 1, 1, 5, 1, 5, 0, 1, 4, 0, 5, 1, 5, 1, 1, 0],
    [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 3, 1, 0, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 3, 5, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 3, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 3, 1, 1, 0, 1, 5, 5, 1]]

private def base4_0 : List ℕ := [7, 12, 12, 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_0 :
    checkGroup 2 107 level3 level4 base4_0 = true := by
  verify_group 2 level3 base4_0 [
    [6, 6, 6, 1, 1, 6, 6, 4]]

private def base4_1 : List ℕ := [10, 12, 12, 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_1 :
    checkGroup 2 107 level3 level4 base4_1 = true := by
  verify_group 2 level3 base4_1 [
    [6, 6, 6, 1, 4, 6, 6, 1], [8, 6, 6, 1, 2, 6, 6, 1],
    [9, 6, 6, 1, 1, 6, 6, 1]]

private def base4_2 : List ℕ := [12, 7, 7, 10]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_2 :
    checkGroup 2 107 level3 level4 base4_2 = true := by
  verify_group 2 level3 base4_2 [
    [6, 1, 6, 6, 6, 6, 1, 4],
    [6, 6, 1, 6, 6, 1, 6, 4]]

private def base4_3 : List ℕ := [12, 7, 10, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_3 :
    checkGroup 2 107 level3 level4 base4_3 = true := by
  verify_group 2 level3 base4_3 [
    [6, 1, 6, 6, 6, 6, 4, 1], [6, 6, 6, 1, 6, 1, 4, 6],
    [10, 6, 2, 1, 2, 1, 8, 6]]

private def base4_4 : List ℕ := [12, 7, 12, 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_4 :
    checkGroup 2 107 level3 level4 base4_4 = true := by
  verify_group 2 level3 base4_4 [
    [6, 6, 6, 1, 6, 1, 6, 4],
    [10, 6, 2, 1, 2, 1, 10, 4]]

private def base4_5 : List ℕ := [12, 10, 12, 2]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_5 :
    checkGroup 2 107 level3 level4 base4_5 = true := by
  verify_group 2 level3 base4_5 [
    [2, 8, 10, 2, 10, 2, 2, 0], [6, 6, 6, 1, 6, 4, 6, 1],
    [10, 4, 6, 1, 2, 6, 6, 1]]

private def base4_6 : List ℕ := [14, 7, 8, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_6 :
    checkGroup 2 107 level3 level4 base4_6 = true := by
  verify_group 2 level3 base4_6 [
    [6, 1, 6, 6, 8, 6, 2, 1], [8, 6, 6, 1, 6, 1, 2, 6],
    [10, 6, 2, 1, 4, 1, 6, 6]]

private def base4_7 : List ℕ := [15, 7, 7, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_7 :
    checkGroup 2 107 level3 level4 base4_7 = true := by
  verify_group 2 level3 base4_7 [
    [6, 1, 6, 6, 9, 6, 1, 1], [6, 6, 1, 6, 9, 1, 6, 1], [9, 1, 6, 6, 6, 6, 1, 1],
    [9, 6, 1, 6, 6, 1, 6, 1],
    [9, 6, 6, 1, 6, 1, 1, 6]]

private def base4_8 : List ℕ := [16, 5, 8, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_8 :
    checkGroup 2 107 level3 level4 base4_8 = true := by
  verify_group 2 level3 base4_8 [
    [6, 1, 6, 6, 10, 4, 2, 1],
    [10, 4, 6, 1, 6, 1, 2, 6]]

private def base4_9 : List ℕ := [16, 6, 7, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_9 :
    checkGroup 2 107 level3 level4 base4_9 = true := by
  verify_group 2 level3 base4_9 [
    [10, 2, 6, 1, 6, 4, 1, 6], [10, 4, 6, 1, 6, 2, 1, 6],
    [10, 5, 6, 1, 6, 1, 1, 6]]

private def base4_10 : List ℕ := [16, 7, 7, 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_10 :
    checkGroup 2 107 level3 level4 base4_10 = true := by
  verify_group 2 level3 base4_10 [
    [10, 6, 6, 0, 6, 1, 1, 6], [10, 6, 6, 1, 6, 1, 1, 5],
    [11, 6, 6, 0, 5, 1, 1, 6]]

private def base4_11 : List ℕ := [16, 7, 8, 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_11 :
    checkGroup 2 107 level3 level4 base4_11 = true := by
  verify_group 2 level3 base4_11 [
    [10, 6, 2, 1, 6, 1, 6, 4], [10, 6, 2, 4, 6, 1, 6, 1],
    [10, 6, 6, 1, 6, 1, 2, 4]]

private def base4_12 : List ℕ := [17, 4, 8, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_12 :
    checkGroup 2 107 level3 level4 base4_12 = true := by
  verify_group 2 level3 base4_12 [
    [11, 3, 6, 1, 6, 1, 2, 6]]

private def base4_13 : List ℕ := [17, 5, 7, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_13 :
    checkGroup 2 107 level3 level4 base4_13 = true := by
  verify_group 2 level3 base4_13 [
    [11, 3, 6, 1, 6, 2, 1, 6],
    [11, 4, 6, 1, 6, 1, 1, 6]]

private def base4_14 : List ℕ := [17, 6, 6, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_14 :
    checkGroup 2 107 level3 level4 base4_14 = true := by
  verify_group 2 level3 base4_14 [
    [11, 5, 5, 1, 6, 1, 1, 6], [11, 5, 6, 1, 6, 1, 0, 6], [11, 6, 5, 1, 6, 0, 1, 6],
    [12, 5, 5, 1, 5, 1, 1, 6]]

private def base4_15 : List ℕ := [17, 6, 7, 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_15 :
    checkGroup 2 107 level3 level4 base4_15 = true := by
  verify_group 2 level3 base4_15 [
    [11, 5, 6, 0, 6, 1, 1, 6], [11, 5, 6, 1, 6, 1, 1, 5], [11, 6, 6, 0, 6, 0, 1, 6],
    [12, 5, 6, 0, 5, 1, 1, 6]]

private def base4_16 : List ℕ := [17, 7, 7, 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_16 :
    checkGroup 2 107 level3 level4 base4_16 = true := by
  verify_group 2 level3 base4_16 [
    [11, 6, 6, 0, 6, 1, 1, 5], [11, 6, 6, 1, 6, 1, 1, 4],
    [12, 6, 6, 0, 5, 1, 1, 5]]

private def base4_17 : List ℕ := [17, 7, 8, 4]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_17 :
    checkGroup 2 107 level3 level4 base4_17 = true := by
  verify_group 2 level3 base4_17 [
    [11, 6, 6, 1, 6, 1, 2, 3]]

private def base4_18 : List ℕ := [18, 4, 7, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_18 :
    checkGroup 2 107 level3 level4 base4_18 = true := by
  verify_group 2 level3 base4_18 [
    [12, 2, 6, 1, 6, 2, 1, 6],
    [12, 3, 6, 1, 6, 1, 1, 6]]

private def base4_19 : List ℕ := [18, 5, 6, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_19 :
    checkGroup 2 107 level3 level4 base4_19 = true := by
  verify_group 2 level3 base4_19 [
    [12, 4, 5, 1, 6, 1, 1, 6], [12, 4, 6, 1, 6, 1, 0, 6], [12, 5, 5, 1, 6, 0, 1, 6],
    [13, 4, 5, 1, 5, 1, 1, 6]]

private def base4_20 : List ℕ := [18, 5, 7, 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_20 :
    checkGroup 2 107 level3 level4 base4_20 = true := by
  verify_group 2 level3 base4_20 [
    [12, 4, 6, 0, 6, 1, 1, 6], [12, 4, 6, 1, 6, 1, 1, 5], [12, 5, 6, 0, 6, 0, 1, 6],
    [13, 4, 6, 0, 5, 1, 1, 6]]

private def base4_21 : List ℕ := [18, 6, 6, 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_21 :
    checkGroup 2 107 level3 level4 base4_21 = true := by
  verify_group 2 level3 base4_21 [
    [12, 5, 5, 0, 6, 1, 1, 6], [12, 5, 5, 1, 6, 1, 1, 5], [12, 5, 6, 0, 6, 1, 0, 6],
    [12, 5, 6, 1, 6, 1, 0, 5], [12, 6, 5, 0, 6, 0, 1, 6], [12, 6, 5, 1, 6, 0, 1, 5],
    [12, 6, 6, 0, 6, 0, 0, 6], [13, 5, 5, 0, 5, 1, 1, 6], [13, 5, 5, 1, 5, 1, 1, 5],
    [13, 5, 6, 0, 5, 1, 0, 6], [13, 6, 5, 0, 5, 0, 1, 6],
    [14, 5, 5, 0, 4, 1, 1, 6]]

private def base4_22 : List ℕ := [18, 6, 7, 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_22 :
    checkGroup 2 107 level3 level4 base4_22 = true := by
  verify_group 2 level3 base4_22 [
    [12, 5, 6, 0, 6, 1, 1, 5], [12, 5, 6, 1, 6, 1, 1, 4], [12, 6, 6, 0, 6, 0, 1, 5],
    [13, 5, 6, 0, 5, 1, 1, 5]]

private def base4_23 : List ℕ := [18, 7, 7, 4]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_23 :
    checkGroup 2 107 level3 level4 base4_23 = true := by
  verify_group 2 level3 base4_23 [
    [12, 6, 6, 0, 6, 1, 1, 4], [12, 6, 6, 1, 6, 1, 1, 3],
    [13, 6, 6, 0, 5, 1, 1, 4]]

private def base4_24 : List ℕ := [19, 4, 5, 8]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_24 :
    checkGroup 2 107 level3 level4 base4_24 = true := by
  verify_group 2 level3 base4_24 [
    [13, 3, 4, 2, 6, 1, 1, 6]]

private def base4_25 : List ℕ := [19, 4, 6, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_25 :
    checkGroup 2 107 level3 level4 base4_25 = true := by
  verify_group 2 level3 base4_25 [
    [13, 3, 4, 1, 6, 1, 2, 6], [13, 3, 5, 1, 6, 1, 1, 6], [13, 3, 6, 1, 6, 1, 0, 6],
    [13, 4, 5, 1, 6, 0, 1, 6],
    [14, 3, 5, 1, 5, 1, 1, 6]]

private def base4_26 : List ℕ := [19, 5, 5, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_26 :
    checkGroup 2 107 level3 level4 base4_26 = true := by
  verify_group 2 level3 base4_26 [
    [13, 3, 4, 1, 6, 2, 1, 6], [13, 4, 3, 1, 6, 1, 2, 6], [13, 4, 4, 1, 6, 1, 1, 6],
    [13, 4, 5, 1, 6, 1, 0, 6], [13, 5, 4, 1, 6, 0, 1, 6], [13, 5, 5, 1, 6, 0, 0, 6],
    [14, 4, 4, 1, 5, 1, 1, 6], [14, 4, 5, 1, 5, 1, 0, 6], [14, 5, 4, 1, 5, 0, 1, 6],
    [15, 4, 4, 1, 4, 1, 1, 6]]

private def base4_27 : List ℕ := [19, 5, 6, 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_27 :
    checkGroup 2 107 level3 level4 base4_27 = true := by
  verify_group 2 level3 base4_27 [
    [13, 4, 5, 0, 6, 1, 1, 6], [13, 4, 5, 1, 6, 1, 1, 5], [13, 4, 6, 0, 6, 1, 0, 6],
    [13, 4, 6, 1, 6, 1, 0, 5], [13, 5, 5, 0, 6, 0, 1, 6], [13, 5, 5, 1, 6, 0, 1, 5],
    [13, 5, 6, 0, 6, 0, 0, 6], [14, 4, 5, 0, 5, 1, 1, 6], [14, 4, 5, 1, 5, 1, 1, 5],
    [14, 4, 6, 0, 5, 1, 0, 6],
    [15, 4, 5, 0, 4, 1, 1, 6]]

private def base4_28 : List ℕ := [19, 6, 6, 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_28 :
    checkGroup 2 107 level3 level4 base4_28 = true := by
  verify_group 2 level3 base4_28 [
    [13, 5, 5, 0, 6, 1, 1, 5], [13, 5, 5, 1, 6, 1, 1, 4], [13, 5, 6, 0, 6, 1, 0, 5],
    [13, 5, 6, 1, 6, 1, 0, 4], [13, 6, 5, 0, 6, 0, 1, 5], [13, 6, 5, 1, 6, 0, 1, 4],
    [13, 6, 6, 0, 6, 0, 0, 5], [14, 5, 5, 0, 5, 1, 1, 5], [14, 5, 5, 1, 5, 1, 1, 4],
    [15, 5, 5, 0, 4, 1, 1, 5]]

private def base4_29 : List ℕ := [20, 4, 5, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_29 :
    checkGroup 2 107 level3 level4 base4_29 = true := by
  verify_group 2 level3 base4_29 [
    [14, 3, 4, 1, 6, 1, 1, 6], [14, 3, 5, 1, 6, 1, 0, 6], [14, 4, 4, 1, 6, 0, 1, 6],
    [14, 4, 5, 1, 6, 0, 0, 6], [15, 3, 4, 1, 5, 1, 1, 6], [15, 3, 5, 1, 5, 1, 0, 6],
    [15, 4, 4, 1, 5, 0, 1, 6]]

private def base4_30 : List ℕ := [20, 5, 5, 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_30 :
    checkGroup 2 107 level3 level4 base4_30 = true := by
  verify_group 2 level3 base4_30 [
    [14, 4, 4, 0, 6, 1, 1, 6], [14, 4, 4, 1, 6, 1, 1, 5], [14, 4, 5, 0, 6, 1, 0, 6],
    [14, 4, 5, 1, 6, 1, 0, 5], [14, 5, 4, 0, 6, 0, 1, 6], [14, 5, 4, 1, 6, 0, 1, 5],
    [15, 4, 4, 0, 5, 1, 1, 6], [15, 4, 4, 1, 5, 1, 1, 5], [15, 4, 5, 0, 5, 1, 0, 6],
    [15, 4, 5, 1, 5, 1, 0, 5], [15, 5, 4, 0, 5, 0, 1, 6],
    [15, 5, 4, 1, 5, 0, 1, 5]]

private def base4_31 : List ℕ := [21, 4, 4, 7]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check4_31 :
    checkGroup 2 107 level3 level4 base4_31 = true := by
  verify_group 2 level3 base4_31 [
    [15, 3, 3, 1, 6, 1, 1, 6], [15, 3, 4, 1, 6, 1, 0, 6], [15, 4, 3, 1, 6, 0, 1, 6],
    [15, 4, 4, 1, 6, 0, 0, 6]]

private def bases4 : List (List ℕ) := [base4_0, base4_1, base4_2, base4_3, base4_4, base4_5, base4_6, base4_7, base4_8, base4_9, base4_10, base4_11, base4_12, base4_13, base4_14, base4_15, base4_16, base4_17, base4_18, base4_19, base4_20, base4_21, base4_22, base4_23, base4_24, base4_25, base4_26, base4_27, base4_28, base4_29, base4_30, base4_31]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
-- Check that the listed common marginals cover the preceding level.
private theorem covers4 :
    (level3.map (dropAxis 2 2)).all (bases4.contains) = true := by
  decide +kernel

private theorem check4 :
    checkGroups 2 107 level3 level4 bases4 = true := by
  simp only [checkGroups, bases4, List.all_cons, List.all_nil,
    check4_0, check4_1, check4_2, check4_3, check4_4, check4_5, check4_6, check4_7, check4_8, check4_9, check4_10, check4_11, check4_12, check4_13, check4_14, check4_15, check4_16, check4_17, check4_18, check4_19, check4_20, check4_21, check4_22, check4_23, check4_24, check4_25, check4_26, check4_27, check4_28, check4_29, check4_30, check4_31, Bool.and_self]

private def level5 : List (List ℕ) := [
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 2, 4, 1, 4, 1, 1, 0]]

private def base5_0 : List ℕ := [2, 8, 10, 2, 10, 2, 2, 0]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_0 :
    checkGroup 3 107 level4 level5 base5_0 = true := by
  verify_group 3 level4 base5_0 [
    [1, 5, 5, 1, 5, 1, 1, 0, 1, 3, 5, 1, 5, 1, 1, 0]]

private def base5_1 : List ℕ := [6, 1, 6, 6, 6, 6, 1, 4]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_1 :
    checkGroup 3 107 level4 level5 base5_1 = true := by
  verify_group 3 level4 base5_1 [
    [5, 1, 1, 5, 1, 5, 0, 1, 1, 0, 5, 1, 5, 1, 1, 3]]

private def base5_2 : List ℕ := [6, 6, 1, 6, 6, 1, 6, 4]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_2 :
    checkGroup 3 107 level4 level5 base5_2 = true := by
  verify_group 3 level4 base5_2 [
    [5, 1, 1, 5, 1, 0, 5, 1, 1, 5, 0, 1, 5, 1, 1, 3]]

private def base5_3 : List ℕ := [6, 6, 6, 1, 1, 6, 6, 4]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_3 :
    checkGroup 3 107 level4 level5 base5_3 = true := by
  verify_group 3 level4 base5_3 [
    [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 0, 1, 1, 3]]

private def base5_4 : List ℕ := [6, 6, 6, 1, 4, 6, 6, 1]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_4 :
    checkGroup 3 107 level4 level5 base5_4 = true := by
  verify_group 3 level4 base5_4 [
    [5, 1, 1, 0, 1, 5, 5, 1, 1, 5, 5, 1, 3, 1, 1, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 3, 5, 5, 1]]

private def base5_5 : List ℕ := [6, 6, 6, 1, 6, 4, 6, 1]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_5 :
    checkGroup 3 107 level4 level5 base5_5 = true := by
  verify_group 3 level4 base5_5 [
    [1, 5, 5, 1, 5, 1, 1, 0, 5, 1, 1, 0, 1, 3, 5, 1],
    [5, 5, 5, 1, 1, 1, 1, 0, 1, 1, 1, 0, 5, 3, 5, 1]]

private def base5_6 : List ℕ := [8, 6, 6, 1, 2, 6, 6, 1]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_6 :
    checkGroup 3 107 level4 level5 base5_6 = true := by
  verify_group 3 level4 base5_6 [
    [5, 1, 1, 0, 1, 5, 5, 1, 3, 5, 5, 1, 1, 1, 1, 0],
    [5, 5, 5, 1, 1, 1, 1, 0, 3, 1, 1, 0, 1, 5, 5, 1]]

private def base5_7 : List ℕ := [9, 1, 6, 6, 6, 6, 1, 1]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_7 :
    checkGroup 3 107 level4 level5 base5_7 = true := by
  verify_group 3 level4 base5_7 [
    [5, 1, 1, 5, 1, 5, 0, 1, 4, 0, 5, 1, 5, 1, 1, 0]]

private def base5_8 : List ℕ := [9, 6, 1, 6, 6, 1, 6, 1]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_8 :
    checkGroup 3 107 level4 level5 base5_8 = true := by
  verify_group 3 level4 base5_8 [
    [5, 1, 1, 5, 1, 0, 5, 1, 4, 5, 0, 1, 5, 1, 1, 0]]

private def base5_9 : List ℕ := [9, 6, 6, 1, 1, 6, 6, 1]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_9 :
    checkGroup 3 107 level4 level5 base5_9 = true := by
  verify_group 3 level4 base5_9 [
    [5, 1, 1, 0, 1, 5, 5, 1, 4, 5, 5, 1, 0, 1, 1, 0]]

private def base5_10 : List ℕ := [10, 4, 6, 1, 2, 6, 6, 1]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_10 :
    checkGroup 3 107 level4 level5 base5_10 = true := by
  verify_group 3 level4 base5_10 [
    [5, 1, 1, 0, 1, 5, 5, 1, 5, 3, 5, 1, 1, 1, 1, 0]]

private def base5_11 : List ℕ := [10, 6, 2, 4, 6, 1, 6, 1]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check5_11 :
    checkGroup 3 107 level4 level5 base5_11 = true := by
  verify_group 3 level4 base5_11 [
    [5, 5, 1, 1, 5, 1, 1, 0, 5, 1, 1, 3, 1, 0, 5, 1]]

private def bases5 : List (List ℕ) := [base5_0, base5_1, base5_2, base5_3, base5_4, base5_5, base5_6, base5_7, base5_8, base5_9, base5_10, base5_11]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
-- Check that the listed common marginals cover the preceding level.
private theorem covers5 :
    (level4.map (dropAxis 3 3)).all (bases5.contains) = true := by
  decide +kernel

private theorem check5 :
    checkGroups 3 107 level4 level5 bases5 = true := by
  simp only [checkGroups, bases5, List.all_cons, List.all_nil,
    check5_0, check5_1, check5_2, check5_3, check5_4, check5_5, check5_6, check5_7, check5_8, check5_9, check5_10, check5_11, Bool.and_self]

private def level6 : List (List ℕ) := []

private def base6_0 : List ℕ := [1, 5, 5, 1, 5, 1, 1, 0, 1, 3, 5, 1, 5, 1, 1, 0]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
-- Check this common marginal by separate closed decisions for its left projections.
private theorem check6_0 :
    checkGroup 4 107 level5 level6 base6_0 = true := by
  verify_group 4 level5 base6_0 [
    [1, 4, 4, 1, 4, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 2, 4, 1, 4, 1, 1, 0]]

private def bases6 : List (List ℕ) := [base6_0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
-- Check that the listed common marginals cover the preceding level.
private theorem covers6 :
    (level5.map (dropAxis 4 4)).all (bases6.contains) = true := by
  decide +kernel

private theorem check6 :
    checkGroups 4 107 level5 level6 bases6 = true := by
  simp only [checkGroups, bases6, List.all_cons, List.all_nil,
    check6_0, Bool.and_self]

/-- At cap 107 the ordered 6-axis projection search is empty. -/
theorem excludeOrdered36 (counts : List ℕ) (hlen : counts.length = 2 ^ 6)
    (hsum : counts.sum = 36) (hcap : ∀ x ∈ counts, x ≤ 2 ^ (8 - 6))
    (hproj : ProjectionConstraints 36 107 6 counts)
    (horder : OrderedProjections 6 counts) : False := by
  have h1 : ∀ t : List ℕ, t.length = 2 ^ 1 → t.sum = 36 →
      (∀ x ∈ t, x ≤ 2 ^ (8 - 1)) → ProjectionConstraints 36 107 1 t →
      OrderedProjections 1 t → t ∈ level1 :=
    fun t hl hs hc hp _ => singles_complete _ _ t hl hs hc hp
  have h2 := complete_of_step (cap := 107) 0 (by decide)
    level1 level2 h1 (checkedStep (covers_bases covers2) check2)
  have h3 := complete_of_step (cap := 107) 1 (by decide)
    level2 level3 h2 (checkedStep (covers_bases covers3) check3)
  have h4 := complete_of_step (cap := 107) 2 (by decide)
    level3 level4 h3 (checkedStep (covers_bases covers4) check4)
  have h5 := complete_of_step (cap := 107) 3 (by decide)
    level4 level5 h4 (checkedStep (covers_bases covers5) check5)
  have h6 := complete_of_step (cap := 107) 4 (by decide)
    level5 level6 h5 (checkedStep (covers_bases covers6) check6)
  exact List.not_mem_nil (h6 counts hlen hsum hcap hproj horder)

#print axioms excludeOrdered36

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8OrderedFiberCapacityCertificate
