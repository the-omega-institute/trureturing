/- GID: D5/S1/Words/Sequenceability/AdaptiveMergePrefix
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/AdaptiveMergePrefix
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Generic two-collision signed-fork obstruction and conditional adaptive repair. -/

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

variable {G : Type*} [AddCommGroup G]

/-- Prefix sum at a cut. -/
def prefixSum (w : List G) (i : ℕ) : G := (w.take i).sum

/-- Every nonempty proper contiguous segment has nonzero sum.

The displayed form is the exact prefix formulation: equality of two prefixes
is equivalent to zero sum of the interval between them, and the only permitted
properly indexed equality is between the two full-word endpoints. -/
def Good (w : List G) : Prop :=
  ∀ ⦃i j : ℕ⦄, i < j → j ≤ w.length →
    prefixSum w i = prefixSum w j → i = 0 ∧ j = w.length

/-- Exact interval formulation, retaining the full-word exception. -/
def ProperIntervals (w : List G) : Prop :=
  ∀ i j : ℕ, i < j → j ≤ w.length → (i ≠ 0 ∨ j ≠ w.length) →
    ((w.drop i).take (j-i)).sum ≠ 0

private lemma interval_prefix_split (w : List G) {i j : ℕ}
    (hij : i ≤ j) :
    prefixSum w i + ((w.drop i).take (j-i)).sum = prefixSum w j := by
  have hs := List.sum_take_add_sum_drop (w.take j) i
  rw [List.take_take, Nat.min_eq_left hij, List.drop_take] at hs
  exact hs

lemma good_iff_proper_intervals (w : List G) : Good w ↔ ProperIntervals w := by
  constructor
  · intro hg i j hij hj hproper hz
    have hs := interval_prefix_split w hij.le
    rw [hz, add_zero] at hs
    obtain ⟨hi0, hjfull⟩ := hg hij hj hs
    exact hproper.elim (fun h => h hi0) (fun h => h hjfull)
  · intro hg i j hij hj heq
    by_contra hend
    have hproper : i ≠ 0 ∨ j ≠ w.length := by tauto
    apply hg i j hij hj hproper
    have hs := interval_prefix_split w hij.le
    rw [← heq] at hs
    apply add_left_cancel (a := prefixSum w i)
    simpa using hs

def LeftCollision (L : List G) (x : G) : Prop :=
  ∃ P S : List G, L = P ++ S ∧ S ≠ [] ∧ S.sum = -x

def RightCollision (R : List G) (y : G) : Prop :=
  ∃ S Q : List G, R = S ++ Q ∧ S ≠ [] ∧ S.sum = -y

private lemma prefixSum_append_left {L T : List G} {i : ℕ} (hi : i ≤ L.length) :
    prefixSum (L ++ T) i = prefixSum L i := by
  simp [prefixSum, List.take_append_of_le_length hi]

private lemma prefixSum_append_right {L T : List G} {i : ℕ} (hi : L.length ≤ i) :
    prefixSum (L ++ T) i = L.sum + prefixSum T (i - L.length) := by
  rw [prefixSum, List.take_append, List.take_of_length_le hi]
  simp [List.sum_append, prefixSum]

private lemma prefixSum_compressed_before (r : G) (L R : List G) {i : ℕ}
    (hi : i ≤ L.length) :
    prefixSum (L ++ [r] ++ R) i = prefixSum L i := by
  simpa only [List.append_assoc] using (prefixSum_append_left (L := L) (T := [r] ++ R) hi)

private lemma prefixSum_compressed_after (r : G) (L R : List G) {j : ℕ}
    (hj : L.length + 1 ≤ j) :
    prefixSum (L ++ [r] ++ R) j = L.sum + r + prefixSum R (j - (L.length + 1)) := by
  rw [List.append_assoc]
  rw [prefixSum_append_right (L := L) (T := [r] ++ R) (by omega)]
  have hj' : 1 ≤ j - L.length := by omega
  have hs := prefixSum_append_right (L := [r]) (T := R)
    (i := j - L.length) (by simpa using hj')
  have heq : j - L.length - 1 = j - (L.length + 1) := by omega
  simpa [heq, add_assoc] using congrArg (L.sum + ·) hs

private lemma prefixSum_expanded_before (x y : G) (L R : List G) {i : ℕ}
    (hi : i ≤ L.length) :
    prefixSum (L ++ [x, y] ++ R) i = prefixSum L i := by
  simpa only [List.append_assoc] using (prefixSum_append_left (L := L) (T := [x, y] ++ R) hi)

private lemma prefixSum_expanded_first (x y : G) (L R : List G) :
    prefixSum (L ++ [x, y] ++ R) (L.length + 1) = L.sum + x := by
  rw [List.append_assoc]
  rw [prefixSum_append_right (L := L) (T := [x, y] ++ R) (by omega)]
  simp [prefixSum]

private lemma prefixSum_expanded_after (x y : G) (L R : List G) {j : ℕ}
    (hj : L.length + 2 ≤ j) :
    prefixSum (L ++ [x, y] ++ R) j = L.sum + x + y +
      prefixSum R (j - (L.length + 2)) := by
  rw [List.append_assoc]
  rw [prefixSum_append_right (L := L) (T := [x, y] ++ R) (by omega)]
  have hj' : 2 ≤ j - L.length := by omega
  have hs := prefixSum_append_right (L := [x,y]) (T := R)
    (i := j - L.length) (by simpa using hj')
  have heq : j - L.length - 2 = j - (L.length + 2) := by omega
  simpa [heq, add_assoc] using congrArg (L.sum + ·) hs

private def oldCut (k i : ℕ) : ℕ := if i ≤ k then i else i - 1

private lemma expanded_old_prefix (x y : G) (L R : List G) {i : ℕ}
    (hne : i ≠ L.length + 1) :
    prefixSum (L ++ [x, y] ++ R) i =
      prefixSum (L ++ [x + y] ++ R) (oldCut L.length i) := by
  by_cases hi : i ≤ L.length
  · simp only [oldCut, if_pos hi]
    rw [prefixSum_expanded_before x y L R hi,
      prefixSum_compressed_before (x + y) L R hi]
  · have hi' : L.length + 2 ≤ i := by omega
    simp only [oldCut, if_neg hi]
    rw [prefixSum_expanded_after x y L R hi',
      prefixSum_compressed_after (x + y) L R (by omega)]
    have hsub : i - 1 - (L.length + 1) = i - (L.length + 2) := by omega
    rw [hsub]
    abel

private lemma inserted_collision {x y : G} {L R : List G} {i : ℕ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hi : i ≤ (L ++ [x, y] ++ R).length)
    (hne : i ≠ L.length + 1)
    (heq : prefixSum (L ++ [x, y] ++ R) i = L.sum + x) :
    LeftCollision L x ∨ RightCollision R y := by
  by_cases hiL : i ≤ L.length
  · left
    rw [prefixSum_expanded_before x y L R hiL] at heq
    have hsum : (L.drop i).sum = -x := by
      have hs := List.sum_take_add_sum_drop L i
      calc
        (L.drop i).sum = L.sum - (L.take i).sum := by
          apply eq_sub_iff_add_eq.mpr
          simpa [add_comm] using hs
        _ = L.sum - (L.sum + x) := by rw [← heq]; rfl
        _ = -x := by abel
    refine ⟨L.take i, L.drop i, (List.take_append_drop i L).symm, ?_, hsum⟩
    intro hnil
    have hxzero : -x = 0 := by simpa [hnil] using hsum.symm
    exact hx (neg_eq_zero.mp hxzero)
  · right
    have hi' : L.length + 2 ≤ i := by omega
    rw [prefixSum_expanded_after x y L R hi'] at heq
    have hs : prefixSum R (i - (L.length + 2)) = -y := by
      apply eq_neg_of_add_eq_zero_right
      have hcancel : y + prefixSum R (i - (L.length + 2)) = 0 := by
        apply add_left_cancel (a := L.sum + x)
        simpa [add_assoc] using heq
      exact hcancel
    refine ⟨R.take (i - (L.length + 2)), R.drop (i - (L.length + 2)),
      (List.take_append_drop _ R).symm, ?_, hs⟩
    intro hnil
    have hyzero : -y = 0 := by simpa [prefixSum, hnil] using hs.symm
    exact hy (neg_eq_zero.mp hyzero)

lemma bad_expand_implies_collision {x y : G} {L R : List G}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hgood : Good (L ++ [x + y] ++ R))
    (hbad : ¬ Good (L ++ [x, y] ++ R)) :
    LeftCollision L x ∨ RightCollision R y := by
  by_contra hnone
  apply hbad
  intro i j hij hj heq
  have hlen : (L ++ [x, y] ++ R).length = L.length + 2 + R.length := by simp only [List.length_append, List.length_cons, List.length_nil] <;> omega
  have hclen : (L ++ [x + y] ++ R).length = L.length + 1 + R.length := by simp only [List.length_append, List.length_cons, List.length_nil] <;> omega
  by_cases hiNew : i = L.length + 1
  · have hjne : j ≠ L.length + 1 := by omega
    have hjhit : prefixSum (L ++ [x, y] ++ R) j = L.sum + x := by
      rw [← heq, hiNew, prefixSum_expanded_first]
    exact (hnone (inserted_collision hx hy hj hjne hjhit)).elim
  · by_cases hjNew : j = L.length + 1
    · have hihit : prefixSum (L ++ [x, y] ++ R) i = L.sum + x := by
        rw [heq, hjNew, prefixSum_expanded_first]
      exact (hnone (inserted_collision hx hy (by omega) hiNew hihit)).elim
    · have hlt : oldCut L.length i < oldCut L.length j := by
        unfold oldCut
        split_ifs <;> omega
      have hle : oldCut L.length j ≤ (L ++ [x + y] ++ R).length := by
        unfold oldCut
        split_ifs <;> omega
      have heq' : prefixSum (L ++ [x + y] ++ R) (oldCut L.length i) =
          prefixSum (L ++ [x + y] ++ R) (oldCut L.length j) := by
        rw [← expanded_old_prefix x y L R hiNew,
          ← expanded_old_prefix x y L R hjNew]
        exact heq
      obtain ⟨hi0, hjfull⟩ := hgood hlt hle heq'
      unfold oldCut at hi0 hjfull
      split_ifs at hi0 hjfull <;> constructor <;> omega


end D5.S1.Words.Sequenceability.AdaptiveMergePrefix
