/- GID: D5/S3/Weil/Separator/TranslationEnergy/Source
   generality: G
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Source
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Construct and control the canonical rational partition for translated energy. -/

import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.TranslationEnergy

open Set
open scoped BigOperators

def hardBreakpoints (R : Nat) (s : Rat) : Finset Rat :=
  {-(2 * (R : Rat)), -(R : Rat), 0, (R : Rat), 2 * (R : Rat),
    s - 2 * (R : Rat), s - (R : Rat), s, s + (R : Rat), s + 2 * (R : Rat)}

def supportHullLower (R : Nat) (s : Rat) : Rat :=
  min (-(2 * (R : Rat))) (s - 2 * (R : Rat))

def supportHullUpper (R : Nat) (s : Rat) : Rat :=
  max (2 * (R : Rat)) (s + 2 * (R : Rat))

def uniformMesh (R : Nat) (s : Rat) (meshDepth : Nat) : Finset Rat :=
  let segments := 2 ^ meshDepth
  let lower := supportHullLower R s
  let upper := supportHullUpper R s
  (Finset.range (segments + 1)).image fun (j : Nat) =>
    lower + (j : Rat) * (upper - lower) / (segments : Rat)

def canonicalPointSet (R : Nat) (s : Rat) (meshDepth : Nat) : Finset Rat :=
  hardBreakpoints R s ∪ uniformMesh R s meshDepth

/-- This is the only source from which translated-energy cells are indexed. -/
def canonicalPoints (R : Nat) (s : Rat) (meshDepth : Nat) : List Rat :=
  (canonicalPointSet R s meshDepth).sort (· ≤ ·)

def cellAt (R : Nat) (s : Rat) (meshDepth i : Nat) : Option (Rat × Rat) := do
  let points := canonicalPoints R s meshDepth
  let lower ← points[i]?
  let upper ← points[i + 1]?
  pure (lower, upper)

def sourceCells (R : Nat) (s : Rat) (meshDepth : Nat) : List (Rat × Rat) :=
  (List.range (canonicalPoints R s meshDepth).length).filterMap fun i =>
    cellAt R s meshDepth i

theorem canonicalPoint_mem_hull (R : Nat) (s x : Rat) (d : Nat)
    (hx : x ∈ canonicalPoints R s d) :
    supportHullLower R s ≤ x ∧ x ≤ supportHullUpper R s := by
  have hardBreakpoint_mem_hull (R : Nat) (s x : Rat)
      (hx : x ∈ hardBreakpoints R s) :
      supportHullLower R s ≤ x ∧ x ≤ supportHullUpper R s := by
    simp only [hardBreakpoints, Finset.mem_insert, Finset.mem_singleton] at hx
    have hR : (0 : Rat) ≤ R := by positivity
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx <;> subst x <;>
      first
      | exact ⟨(min_le_left _ _).trans (by linarith),
          (by linarith : _ ≤ 2 * (R : Rat)).trans (le_max_left _ _)⟩
      | exact ⟨(min_le_right _ _).trans (by linarith),
          (by linarith : _ ≤ s + 2 * (R : Rat)).trans (le_max_right _ _)⟩
  have uniformMesh_mem_hull (R : Nat) (s x : Rat) (d : Nat)
      (hx : x ∈ uniformMesh R s d) :
      supportHullLower R s ≤ x ∧ x ≤ supportHullUpper R s := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hj' : j ≤ 2 ^ d := by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hj
    have hn : (0 : Rat) < (2 ^ d : Nat) := by positivity
    have hlo : supportHullLower R s ≤ supportHullUpper R s := by
      calc
        supportHullLower R s ≤ -(2 * (R : Rat)) := min_le_left _ _
        _ ≤ 2 * (R : Rat) := by
          have hR : (0 : Rat) ≤ R := by positivity
          linarith
        _ ≤ supportHullUpper R s := le_max_left _ _
    constructor
    · apply le_add_of_nonneg_right
      exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hlo)) hn.le
    · have hjq : (j : Rat) ≤ (2 ^ d : Nat) := by exact_mod_cast hj'
      calc
        supportHullLower R s + (j : Rat) *
            (supportHullUpper R s - supportHullLower R s) / (2 ^ d : Nat)
            ≤ supportHullLower R s + ((2 ^ d : Nat) : Rat) *
                (supportHullUpper R s - supportHullLower R s) / (2 ^ d : Nat) := by
                  gcongr
        _ = supportHullUpper R s := by
          field_simp [show (((2 ^ d : Nat) : Rat) : Rat) ≠ 0 by positivity]
          ring
  rw [canonicalPoints, Finset.mem_sort] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact hardBreakpoint_mem_hull R s x hx
  · exact uniformMesh_mem_hull R s x d hx

theorem canonicalPoints_first (R : Nat) (s : Rat) (d : Nat) :
    (canonicalPoints R s d)[0]? = some (supportHullLower R s) := by
  have hlo : supportHullLower R s ∈ canonicalPoints R s d := by
    rw [canonicalPoints, Finset.mem_sort]
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by positivity), ?_⟩
    simp [uniformMesh]
  obtain ⟨j, hj, hjval⟩ := List.getElem_of_mem hlo
  have hpos : 0 < (canonicalPoints R s d).length := by omega
  rw [List.getElem?_eq_getElem hpos]
  congr 1
  apply le_antisymm
  · rw [← hjval]
    exact (Finset.sortedLT_sort (canonicalPointSet R s d)).sortedLE.getElem_le_getElem_of_le (Nat.zero_le j)
  · exact (canonicalPoint_mem_hull R s _ d (List.getElem_mem _)).1

theorem canonicalPoints_last (R : Nat) (s : Rat) (d : Nat) :
    (canonicalPoints R s d)[(canonicalPoints R s d).length - 1]? =
      some (supportHullUpper R s) := by
  have hup : supportHullUpper R s ∈ canonicalPoints R s d := by
    rw [canonicalPoints, Finset.mem_sort]
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨2 ^ d, Finset.mem_range.mpr (by omega), ?_⟩
    simp [uniformMesh]
  obtain ⟨j, hj, hjval⟩ := List.getElem_of_mem hup
  have hpos : 0 < (canonicalPoints R s d).length := by omega
  have hlast : (canonicalPoints R s d).length - 1 <
      (canonicalPoints R s d).length := by omega
  rw [List.getElem?_eq_getElem hlast]
  congr 1
  apply le_antisymm
  · exact (canonicalPoint_mem_hull R s _ d (List.getElem_mem _)).2
  · rw [← hjval]
    exact (Finset.sortedLT_sort (canonicalPointSet R s d)).sortedLE.getElem_le_getElem_of_le (by omega)

theorem sourceCells_eq_map (R : Nat) (s : Rat) (d : Nat) :
    sourceCells R s d =
      (List.range ((canonicalPoints R s d).length - 1)).map fun i =>
        ((canonicalPoints R s d).getD i 0,
          (canonicalPoints R s d).getD (i + 1) 0) := by
  let points := canonicalPoints R s d
  let n := points.length - 1
  have hpos : 0 < points.length := by
    have hne : (canonicalPointSet R s d).Nonempty := by
      refine ⟨supportHullLower R s, Finset.mem_union_right _ ?_⟩
      refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by positivity), ?_⟩
      simp [uniformMesh]
    simpa [points, canonicalPoints, Finset.length_sort] using Finset.card_pos.mpr hne
  have hn : points.length = n + 1 := by simp only [n]; omega
  have hmap : (List.range n).filterMap (fun i => cellAt R s d i) =
      (List.range n).map fun i => (points.getD i 0, points.getD (i + 1) 0) := by
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro i hi
    have hi' : i < n := List.mem_range.mp hi
    have hiCell : i + 1 < (canonicalPoints R s d).length := by
      change i + 1 < points.length
      rw [hn]
      omega
    have hicell := (show cellAt R s d i = some ((canonicalPoints R s d)[i],
        (canonicalPoints R s d)[i + 1]) from by
        simp [cellAt, List.getElem?_eq_getElem, hiCell,
          show i < (canonicalPoints R s d).length by omega])
    rw [hicell]
    congr 2
    · exact (List.getD_eq_getElem (canonicalPoints R s d) 0 (by omega)).symm
    · exact (List.getD_eq_getElem (canonicalPoints R s d) 0 hiCell).symm
  have hlast : cellAt R s d n = none := by
    have hnlt : n < points.length := by omega
    have hnnot : ¬ n + 1 < points.length := by omega
    rw [cellAt]
    simp [points, List.getElem?_eq_getElem hnlt, List.getElem?_eq_none (Nat.le_of_not_gt hnnot)]
  change (List.range points.length).filterMap (fun i => cellAt R s d i) = _
  rw [hn, List.range_succ, List.filterMap_append, hmap]
  simp [hlast, n, points]

theorem sourceCells_index (R : Nat) (s : Rat) (d i : Nat)
    (hi : i + 1 < (canonicalPoints R s d).length) :
    (sourceCells R s d)[i]? = cellAt R s d i := by
  have hirange : i < (List.range ((canonicalPoints R s d).length - 1)).length := by
    simp only [List.length_range]
    omega
  rw [sourceCells_eq_map, List.getElem?_map, List.getElem?_eq_getElem hirange]
  simp only [List.getElem_range]
  rw [(show cellAt R s d i = some ((canonicalPoints R s d)[i],
        (canonicalPoints R s d)[i + 1]) from by
        simp [cellAt, List.getElem?_eq_getElem, hi,
          show i < (canonicalPoints R s d).length by omega])]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  exact ⟨List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi⟩

theorem sourceCells_length_add_one (R : Nat) (s : Rat) (d : Nat) :
    (sourceCells R s d).length + 1 = (canonicalPoints R s d).length := by
  rw [sourceCells_eq_map, List.length_map, List.length_range]
  have hpos : 0 < (canonicalPoints R s d).length := by
    have hne : (canonicalPointSet R s d).Nonempty := by
      refine ⟨supportHullLower R s, Finset.mem_union_right _ ?_⟩
      refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by positivity), ?_⟩
      simp [uniformMesh]
    simpa [canonicalPoints, Finset.length_sort] using Finset.card_pos.mpr hne
  omega

theorem cellAt_no_canonicalPoint_between (R : Nat) (s : Rat) (d i : Nat) (a b x : Rat)
    (hcell : cellAt R s d i = some (a, b)) (hx : x ∈ canonicalPoints R s d) :
    ¬ (a < x ∧ x < b) := by
  have hi : i + 1 < (canonicalPoints R s d).length := by
    by_contra hn
    have hnone := List.getElem?_eq_none (l := canonicalPoints R s d) (Nat.le_of_not_gt hn)
    have hi0 : i < (canonicalPoints R s d).length := by
      by_contra hn0
      have hnone0 := List.getElem?_eq_none (l := canonicalPoints R s d)
        (Nat.le_of_not_gt hn0)
      simp [cellAt, hnone0] at hcell
    rw [cellAt, List.getElem?_eq_getElem hi0, hnone] at hcell
    simp at hcell
  have hidx := (show cellAt R s d i = some ((canonicalPoints R s d)[i],
        (canonicalPoints R s d)[i + 1]) from by
        simp [cellAt, List.getElem?_eq_getElem, hi,
          show i < (canonicalPoints R s d).length by omega])
  rw [hcell] at hidx
  injection hidx with hpair
  injection hpair with ha hb
  obtain ⟨j, hj, hjval⟩ := List.getElem_of_mem hx
  intro hab
  by_cases hji : j ≤ i
  · have hxa : x ≤ a := by
      rw [ha, ← hjval]
      exact (Finset.sortedLT_sort (canonicalPointSet R s d)).sortedLE.getElem_le_getElem_of_le hji
    exact (not_lt_of_ge hxa) hab.1
  · have hij : i + 1 ≤ j := by omega
    have hbx : b ≤ x := by
      rw [hb, ← hjval]
      exact (Finset.sortedLT_sort (canonicalPointSet R s d)).sortedLE.getElem_le_getElem_of_le hij
    exact (not_lt_of_ge hbx) hab.2

theorem cellAt_gap_le_mesh (R : Nat) (s : Rat) (d i : Nat) (a b : Rat)
    (hR : 0 < R) (hcell : cellAt R s d i = some (a, b)) :
    b - a ≤ (supportHullUpper R s - supportHullLower R s) / ((2 ^ d : Nat) : Rat) := by
  have cellAt_mem_canonicalPoints (R : Nat) (s : Rat) (d i : Nat) (a b : Rat)
      (hcell : cellAt R s d i = some (a, b)) :
      a ∈ canonicalPoints R s d ∧ b ∈ canonicalPoints R s d := by
    have hi : i < (canonicalPoints R s d).length := by
      by_contra hn
      have hnone := List.getElem?_eq_none (l := canonicalPoints R s d) (Nat.le_of_not_gt hn)
      simp [cellAt, hnone] at hcell
    have hj : i + 1 < (canonicalPoints R s d).length := by
      by_contra hn
      have hnone := List.getElem?_eq_none (l := canonicalPoints R s d) (Nat.le_of_not_gt hn)
      rw [cellAt, List.getElem?_eq_getElem hi, hnone] at hcell
      simp at hcell
    have hidx := (show cellAt R s d i = some ((canonicalPoints R s d)[i],
          (canonicalPoints R s d)[i + 1]) from by
          simp [cellAt, List.getElem?_eq_getElem, hj,
            show i < (canonicalPoints R s d).length by omega])
    rw [hcell] at hidx
    injection hidx with hpair
    injection hpair with ha hb
    subst a
    subst b
    exact ⟨List.getElem_mem _, List.getElem_mem _⟩
  let lower := supportHullLower R s
  let upper := supportHullUpper R s
  let segments : Nat := 2 ^ d
  let step : Rat := (upper - lower) / segments
  have hsegments : (0 : Rat) < segments := by positivity
  have hhull : lower < upper := by
    have hr : (0 : Rat) < R := by exact_mod_cast hR
    exact (min_le_left _ _).trans_lt ((show -(2 * (R : Rat)) < 2 * R by
      linarith).trans_le (le_max_left _ _))
  have hstep : 0 < step := div_pos (sub_pos.mpr hhull) hsegments
  have hmem := cellAt_mem_canonicalPoints R s d i a b hcell
  have haHull := (canonicalPoint_mem_hull R s a d hmem.1).1
  have hbHull := (canonicalPoint_mem_hull R s b d hmem.2).2
  change b - a ≤ step
  by_contra hgap
  have hgap' : step < b - a := lt_of_not_ge hgap
  let q : Rat := (a - lower) / step
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr haHull) hstep.le
  let j : Nat := ⌊q⌋₊ + 1
  let x : Rat := lower + (j : Rat) * step
  have hqj : q < (j : Rat) := by
    simpa only [j, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one q
  have hja : a < x := by
    have := (div_lt_iff₀ hstep).mp hqj
    dsimp only [q, x] at this ⊢
    linarith
  have hfloor : ((⌊q⌋₊ : Nat) : Rat) ≤ q := Nat.floor_le hq
  have hxle : x ≤ a + step := by
    have hm := mul_le_mul_of_nonneg_right hfloor hstep.le
    dsimp only [q, j, x] at hm ⊢
    push_cast at hm ⊢
    have hcancel : (a - lower) / step * step = a - lower :=
      div_mul_cancel₀ _ hstep.ne'
    rw [hcancel] at hm
    linarith
  have hxb : x < b := hxle.trans_lt (by linarith)
  have hxupper : x ≤ upper := hxb.le.trans hbHull
  have hsegmentEq : lower + (segments : Rat) * step = upper := by
    dsimp only [step]
    field_simp [hsegments.ne']
    ring
  have hjle : j ≤ segments := by
    have hjcast : (j : Rat) ≤ (segments : Rat) := by
      have := hxupper
      rw [← hsegmentEq] at this
      dsimp only [x] at this
      have hmul : (j : Rat) * step ≤ (segments : Rat) * step :=
        (add_le_add_iff_left lower).mp this
      exact (mul_le_mul_iff_right₀ hstep).mp (by simpa [mul_comm] using hmul)
    exact_mod_cast hjcast
  have hxmesh : x ∈ uniformMesh R s d := by
    refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by dsimp only [segments] at hjle ⊢; omega), ?_⟩
    dsimp only [uniformMesh, x, step, lower, upper, segments]
    ring
  have hxcanon : x ∈ canonicalPoints R s d := by
    rw [canonicalPoints, Finset.mem_sort]
    exact Finset.mem_union_right _ hxmesh
  exact cellAt_no_canonicalPoint_between R s d i a b x hcell hxcanon ⟨hja, hxb⟩

end D5.S3.Weil.Separator.TranslationEnergy
