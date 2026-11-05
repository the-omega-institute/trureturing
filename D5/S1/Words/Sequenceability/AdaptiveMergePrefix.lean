/- GID: D5/S1/Words/Sequenceability/AdaptiveMergePrefix
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/AdaptiveMergePrefix
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Generic two-collision signed-fork obstruction and conditional adaptive repair. -/

import D5.S1.Words.Sequenceability.SeparatedPrefixReflection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-!
Generic prefix characterization and the single inserted-cut obstruction.
The only allowed prefix equality joins the two full-word endpoints, including
when the full sum is zero. No torsion or ambient-finiteness premise is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S1.Words.Sequenceability.AdaptiveMergePrefix

open scoped Classical

open scoped BigOperators

open _root_.D5.S1.Words.Sequenceability

variable {G : Type*} [AddCommGroup G]

/-- Prefix sum at a cut. -/
def prefixSum (w : List G) (i : ℕ) : G := SeparatedPrefixReflection.pref w i

/-- Every nonempty proper contiguous segment has nonzero sum.

The displayed form is the exact prefix formulation: equality of two prefixes
is equivalent to zero sum of the interval between them, and the only permitted
properly indexed equality is between the two full-word endpoints. -/
def Good (w : List G) : Prop :=
  ∀ ⦃i j : ℕ⦄, i < j → j ≤ w.length →
    prefixSum w i = prefixSum w j → i = 0 ∧ j = w.length

/-- Exact interval formulation, retaining the full-word exception. -/
def ProperIntervals (w : List G) : Prop := SeparatedPrefixReflection.Good w

/-- Consumed equivalence adapter for the original interval API. -/
lemma good_iff_proper_intervals (w : List G) : Good w ↔ ProperIntervals w := by
  exact (SeparatedPrefixReflection.good_iff w).symm

def LeftCollision (L : List G) (x : G) : Prop :=
  ∃ P S : List G, L = P ++ S ∧ S ≠ [] ∧ S.sum = -x

def RightCollision (R : List G) (y : G) : Prop :=
  ∃ S Q : List G, R = S ++ Q ∧ S ≠ [] ∧ S.sum = -y

lemma bad_expand_implies_collision {x y : G} {L R : List G}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hgood : Good (L ++ [x + y] ++ R))
    (hbad : ¬ Good (L ++ [x, y] ++ R)) :
    LeftCollision L x ∨ RightCollision R y := by
  have hcol : L.sum + x ∈ SeparatedPrefixReflection.inventory (L ++ (x + y) :: R) := by
    by_contra hn
    have ho : SeparatedPrefixReflection.Good (L ++ (x + y) :: R) := by
      simpa only [ProperIntervals, List.append_assoc, List.cons_append, List.nil_append] using
        (good_iff_proper_intervals _).mp hgood
    have he := SeparatedPrefixReflection.expansion_good L R x y ho hn
    apply hbad
    apply (good_iff_proper_intervals _).mpr
    simpa only [ProperIntervals, List.append_assoc, List.cons_append, List.nil_append] using he
  obtain ⟨i, _, heq⟩ := SeparatedPrefixReflection.mem_inventory.mp hcol
  by_cases hiL : i ≤ L.length
  · left
    rw [SeparatedPrefixReflection.pref_append_left L ((x + y) :: R) hiL] at heq
    have hsum : (L.drop i).sum = -x := by
      have hs := List.sum_take_add_sum_drop L i
      change SeparatedPrefixReflection.pref L i + (L.drop i).sum = L.sum at hs
      rw [heq] at hs
      apply eq_neg_of_add_eq_zero_right
      apply add_left_cancel (a := L.sum)
      simpa only [add_assoc, add_zero] using hs
    refine ⟨L.take i, L.drop i, (List.take_append_drop i L).symm, ?_, hsum⟩
    intro hnil
    have hxzero : -x = 0 := by simpa [hnil] using hsum.symm
    exact hx (neg_eq_zero.mp hxzero)
  · right
    rw [SeparatedPrefixReflection.pref_append_right L ((x + y) :: R) (by omega)] at heq
    have hsub : i - L.length - 1 = i - (L.length + 1) := by omega
    have hpr : SeparatedPrefixReflection.pref ((x + y) :: R) (i - L.length) =
        x + y + SeparatedPrefixReflection.pref R (i - (L.length + 1)) := by
      simpa only [List.cons_append, List.nil_append, List.length_singleton, List.sum_singleton, hsub] using
        SeparatedPrefixReflection.pref_append_right [x + y] R (j := i - L.length) (by simp; omega)
    rw [hpr] at heq
    have hs : (R.take (i - (L.length + 1))).sum = -y := by
      apply eq_neg_of_add_eq_zero_right
      apply add_left_cancel (a := L.sum + x)
      simpa only [← add_assoc, add_zero, SeparatedPrefixReflection.pref] using heq
    refine ⟨R.take (i - (L.length + 1)), R.drop (i - (L.length + 1)),
      (List.take_append_drop _ R).symm, ?_, hs⟩
    intro hnil
    have hyzero : -y = 0 := by simpa [hnil] using hs.symm
    exact hy (neg_eq_zero.mp hyzero)


end D5.S1.Words.Sequenceability.AdaptiveMergePrefix
