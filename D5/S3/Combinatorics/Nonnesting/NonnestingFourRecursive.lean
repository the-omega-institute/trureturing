/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourRecursive
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourRecursive
   mirror-E: none(waiver:row-four-increasing-recursion)
   anchors: []
   utility: none
   digest: Recovers an increasing-order word from its least-value deletion. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourIncreasing
import D5.S3.Combinatorics.Nonnesting.NonnestingFourInsert

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourRecursive

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingFourIncreasing

theorem increasing_reconstruct (w : List ℕ) (n : ℕ)
    (hw : w ∈ NonnestingDefs.avoiders (n + 1)
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
    (hn : 1 ≤ n)
    (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n + 1 →
      (w).idxOf a < (w).idxOf b) :
    let v := (w.filter (fun x => decide (1 < x))).map (fun x => x - 1)
    w = directSum 1 [1, 1] v ∨
      ∃ r : List ℕ, v = 1 :: r ∧ w = 1 :: 2 :: 1 :: shift 1 r := by
  let v := (w.filter (fun x => decide (1 < x))).map (fun x => x - 1)
  have hcount1 : w.count 1 = 2 := by
    apply doubled_count (n + 1) 1 w hw.1
    rw [List.mem_range'_1]
    omega
  have hpositive : ∀ x ∈ w, 1 ≤ x := by
    intro x hx
    have hxbase : x ∈ (List.range' 1 (n + 1)).flatMap (fun i => [i, i]) :=
      hw.1.mem_iff.mp hx
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
    have heq : x = i := by simpa using hxi
    subst x
    rw [List.mem_range'_1] at hi
    omega
  have hprefix := increasing_prefix w (n + 1) hw (by omega) hfirst
  rcases hprefix with ⟨t, heq⟩ | ⟨t, heq⟩
  · have htNot : 1 ∉ t := by
      intro ht
      have hpos : 0 < t.count 1 := List.count_pos_iff.mpr ht
      rw [heq] at hcount1
      simp at hcount1
      omega
    have htPos : ∀ x ∈ t, 1 < x := by
      intro x hx
      have hp : 1 ≤ x := hpositive x (by rw [heq]; simp [hx])
      have hne : x ≠ 1 := by
        intro h
        subst x
        exact htNot hx
      omega
    have htFilter : t.filter (fun x => decide (1 < x)) = t := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp [htPos x hx]
    have hfilter : w.filter (fun x => decide (1 < x)) = 2 :: t := by
      rw [heq]
      simp [htFilter]
    have hrestore : shift 1 v = 2 :: t := by
      rw [show v = (2 :: t).map (fun x => x - 1) by simp [v, hfilter]]
      simp only [shift, List.map_map, List.map_cons]
      congr 1
      calc
        t.map ((fun x => x + 1) ∘ (fun x => x - 1)) = t.map id := by
          apply List.map_congr_left
          intro x hx
          simp only [Function.comp_apply, id_eq]
          have := htPos x hx
          omega
        _ = t := List.map_id t
    left
    change w = 1 :: 1 :: shift 1 v
    rw [heq, hrestore]
  · have htNot : 1 ∉ t := by
      intro ht
      have hpos : 0 < t.count 1 := List.count_pos_iff.mpr ht
      rw [heq] at hcount1
      simp at hcount1
      omega
    have htPos : ∀ x ∈ t, 1 < x := by
      intro x hx
      have hp : 1 ≤ x := hpositive x (by rw [heq]; simp [hx])
      have hne : x ≠ 1 := by
        intro h
        subst x
        exact htNot hx
      omega
    have htFilter : t.filter (fun x => decide (1 < x)) = t := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp [htPos x hx]
    have hfilter : w.filter (fun x => decide (1 < x)) = 2 :: t := by
      rw [heq]
      simp [htFilter]
    have hv : v = 1 :: t.map (fun x => x - 1) := by
      simp [v, hfilter]
    have hrestore : shift 1 (t.map (fun x => x - 1)) = t := by
      simp only [shift, List.map_map]
      calc
        t.map ((fun x => x + 1) ∘ (fun x => x - 1)) = t.map id := by
          apply List.map_congr_left
          intro x hx
          simp only [Function.comp_apply, id_eq]
          have := htPos x hx
          omega
        _ = t := List.map_id t
    refine Or.inr ⟨t.map (fun x => x - 1), hv, ?_⟩
    rw [heq, hrestore]

end D5.S3.Combinatorics.Nonnesting.NonnestingFourRecursive

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourRecursive.increasing_reconstruct
