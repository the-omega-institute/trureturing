/- GID: D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/DihedralConstructions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full retained reflection-subgroup total-code constructions in actual dihedral groups. -/

import D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

/-!
The retained constructions of Jun-Yang Zhang, arXiv:2210.03336v1,
Examples 5.6--5.8, as distinguished from the false exhaustiveness in
Theorem 5.10 by Ma--Nikandish--Zhang's revised correction. All vertices
are elements of the actual dihedral group; the graph excludes loops.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.DihedralConstructions

open DihedralGroup
open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

variable {n : ℕ}

/-- The complete order-two reflection subgroup, for any reflection. -/
def reflectionSubgroup (c : ZMod n) : Subgroup (DihedralGroup n) where
  carrier := {g | g = 1 ∨ g = sr c}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  inv_mem' := by rintro a (rfl | rfl) <;> simp

/-- The full set of reflections. -/
def reflections : Set (DihedralGroup n) := {g | ∃ i, g = sr i}

theorem reflections_normal : NormalSubset (reflections (n := n)) := by
  rintro (i | i) _ ⟨j, rfl⟩ <;>
    simp only [reflections, Set.mem_setOf_eq, inv_r, inv_sr, r_mul_sr,
      sr_mul_sr, sr_mul_r, r_mul_r] <;> exact ⟨_, rfl⟩

/-- The all-reflection graph is exactly the complete bipartite graph on
the rotation and reflection parts, including all n elements of each part. -/
theorem reflections_adjacency (g h : DihedralGroup n) :
    (sumGraph reflections reflections_normal).Adj g h ↔
      (∃ i j, g = r i ∧ h = sr j) ∨ (∃ i j, g = sr i ∧ h = r j) := by
  cases g <;> cases h <;>
    simp [sumGraph, reflections, r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr]

/-- Every reflection subgroup is a total code in the full all-reflection
graph. No parity or lower bound on n is required for this construction. -/
theorem reflections_total (c : ZMod n) :
    IsTotalPerfectCode (sumGraph (reflections (n := n)) reflections_normal)
      (reflectionSubgroup c : Set (DihedralGroup n)) := by
  intro g
  cases g with
  | r i =>
    refine ⟨sr c, ⟨Or.inr rfl, ?_⟩, ?_⟩
    · rw [reflections_adjacency]; exact Or.inl ⟨i, c, rfl, rfl⟩
    · rintro h ⟨hh, he⟩
      rcases hh with rfl | rfl
      · change r i ≠ 1 ∧ r i * 1 ∈ reflections at he
        obtain ⟨j, hj⟩ := he.2
        simpa using hj
      · rfl
  | sr i =>
    refine ⟨1, ⟨Or.inl rfl, ?_⟩, ?_⟩
    · rw [reflections_adjacency]; exact Or.inr ⟨i, 0, rfl, rfl⟩
    · rintro h ⟨hh, he⟩
      rcases hh with rfl | rfl
      · rfl
      · rw [reflections_adjacency] at he; simpa using he

/-- The even/odd reflection-class construction. The additive character is
the ordinary parity map in the source application n=2*l. -/
def parityConnection (e : ZMod n →+ ZMod 2) (c : ZMod n) :
    Set (DihedralGroup n)
  | r i => e i = 1
  | sr i => e i = e c

@[simp] private theorem mem_parity_r (e : ZMod n →+ ZMod 2) (c i : ZMod n) :
    r i ∈ parityConnection e c ↔ e i = 1 := Iff.rfl

@[simp] private theorem mem_parity_sr (e : ZMod n →+ ZMod 2) (c i : ZMod n) :
    sr i ∈ parityConnection e c ↔ e i = e c := Iff.rfl

private theorem neg_two (x : ZMod 2) : -x = x := ZMod.neg_eq_self_mod_two x

theorem parity_normal (e : ZMod n →+ ZMod 2) (c : ZMod n) :
    NormalSubset (parityConnection e c) := by
  rintro (i | i) (j | j) hj <;>
    simp only [inv_r, inv_sr, r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr,
      mem_parity_r, mem_parity_sr, map_add, map_sub, map_neg] at *
  · simpa [add_right_comm, CharTwo.add_self_eq_zero] using hj
  · simpa only [sub_eq_add_neg, neg_two, CharTwo.add_cancel_right] using hj
  · simpa [neg_two, add_right_comm, CharTwo.add_self_eq_zero] using hj
  · simp only [sub_eq_add_neg, neg_two]
    rw [add_comm (e j) (e i), CharTwo.add_cancel_left]
    exact hj

/-- Both retained parity families, for every reflection c. This proves
the full construction, including the source c=0 and c=-1 instances. -/
theorem parity_total (e : ZMod n →+ ZMod 2) (c : ZMod n) :
    IsTotalPerfectCode (sumGraph (parityConnection e c) (parity_normal e c))
      (reflectionSubgroup c) := by
  classical
  intro g
  have heq (x y : ZMod 2) : x - y = 1 ↔ x ≠ y := by
    revert x y
    decide +kernel
  cases g with
  | r i =>
    by_cases hi : e i = 1
    · refine ⟨1, ⟨Or.inl rfl, ?_⟩, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro h; have h0 : i = 0 := r.inj h; simpa [h0] using hi
        · simpa [parityConnection] using hi
      · rintro h ⟨hh, hne, hm⟩
        rcases hh with rfl | rfl
        · rfl
        · change e (c - i) = e c at hm
          simp only [map_sub] at hm
          have : e i = 0 := sub_eq_self.mp hm
          exact ((zero_ne_one : (0 : ZMod 2) ≠ 1)
            (by simpa [this] using hi)).elim
    · have hi0 : e i = 0 := by
        have := (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (e i)
        exact this.resolve_right hi
      refine ⟨sr c, ⟨Or.inr rfl, ?_⟩, ?_⟩
      · refine ⟨by simp, ?_⟩
        change e (c - i) = e c; simp [hi0]
      · rintro h ⟨hh, hne, hm⟩
        rcases hh with rfl | rfl
        · exact (hi (by simpa [parityConnection] using hm)).elim
        · rfl
  | sr i =>
    by_cases hi : e i = e c
    · refine ⟨1, ⟨Or.inl rfl, ?_⟩, ?_⟩
      · exact ⟨by simp [← r_zero], by simpa [parityConnection] using hi⟩
      · rintro h ⟨hh, hne, hm⟩
        rcases hh with rfl | rfl
        · rfl
        · change e (c - i) = 1 at hm
          simp [map_sub, hi] at hm
    · refine ⟨sr c, ⟨Or.inr rfl, ?_⟩, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro h; exact hi (congrArg e (sr.inj h))
        · change e (c - i) = 1
          rw [map_sub]
          exact (heq _ _).mpr (Ne.symm hi)
      · rintro h ⟨hh, hne, hm⟩
        rcases hh with rfl | rfl
        · exact (hi (by simpa [parityConnection] using hm)).elim
        · rfl

/-- The actual source parity character on every even rotation group. -/
def parity (l : ℕ) : ZMod (2 * l) →+ ZMod 2 :=
  (ZMod.castHom (dvd_mul_right 2 l) (ZMod 2)).toAddMonoidHom

#print axioms reflections_total
#print axioms parity_total

end D5.S3.Combinatorics.CayleySumCodes.DihedralConstructions
