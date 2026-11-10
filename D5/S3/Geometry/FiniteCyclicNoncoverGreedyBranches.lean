/- GID: D5/S3/Geometry/FiniteCyclicNoncoverGreedyBranches
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCyclicNoncoverGreedyBranches
   mirror-E: none(waiver:original-cyclic-second-round)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Actual original s2 no/yes branches and their later-round restrictions, without altering ambient labels. -/
import D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction

/-! UNCOMPILED source. The branches below are exact original-ground remaining
families. Their identification with inserted/shifted FREE interval path families
and the arithmetic critical-face readback remain separate missing C01 work. -/

noncomputable section
open Finset

namespace D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches
open FiniteCoordinateGreedyMatching FiniteGreedyFamilyTransport
open FiniteCyclicNoncoverCollapse FiniteCyclicNoncoverGreedyReduction

variable {V : Type*} [Fintype V] [DecidableEq V]

def branchA {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) : Finset (Finset V) :=
  (tailFaces (by omega) s).filter fun a => s ⟨1, by omega⟩ ∉ a ∧ s ⟨n-1, by omega⟩ ∈ a

def branchB {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) : Finset (Finset V) :=
  (tailFaces (by omega) s).filter fun a => s ⟨1, by omega⟩ ∈ a ∧ s ⟨2, by omega⟩ ∉ a

private theorem label_ne {n : Nat} (s : Fin n ↪ V) (i j : Fin n) (h : i.val ≠ j.val) :
    s i ≠ s j := fun he => h (congrArg Fin.val (s.injective he))

private theorem succ_val {n : Nat} (i : Fin n) (h : i.val+1 < n) :
    (successor (show 0 < n by omega) i).val = i.val+1 := Nat.mod_eq_of_lt h

private theorem succ_one {n : Nat} (hn : 6 ≤ n) :
    successor (show 0 < n by omega) ⟨1, by omega⟩ = (⟨2, by omega⟩ : Fin n) := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (by omega)

private theorem tail_insert_iff {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (a : Finset V)
    (ha : a ∈ tailFaces (by omega) s) :
    insert (s ⟨1, by omega⟩) a ∈ tailFaces (by omega) s ↔ s ⟨n-1, by omega⟩ ∉ a := by
  obtain ⟨_, hne, hsupp, hp, hind, hend⟩ := Finset.mem_filter.mp ha
  have hlw : s ⟨n-1, by omega⟩ ≠ s ⟨1, by omega⟩ := label_ne s _ _ (by dsimp; omega)
  have hpw : point (by omega) s ≠ s ⟨1, by omega⟩ := label_ne s _ _ (by dsimp [pointIndex]; omega)
  constructor
  · intro h
    have he := (Finset.mem_filter.mp h).2.2.2.2.2
    rcases he with h | h
    · exact (h (Finset.mem_insert_self _ _)).elim
    · exact fun hm => h (Finset.mem_insert_of_mem hm)
  · intro hl
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.insert_nonempty _ _,
      Finset.insert_subset (spoke_mem_ground s _) hsupp, ?_, ?_, Or.inr ?_⟩
    · simpa [hpw] using hp
    · intro i hi hib
      exact (hind i hi hib).imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem
    · simpa [hlw] using hl

private theorem tail_erase_iff {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (a : Finset V)
    (ha : a ∈ tailFaces (by omega) s) :
    a.erase (s ⟨1, by omega⟩) ∈ tailFaces (by omega) s ↔ s ⟨2, by omega⟩ ∈ a := by
  obtain ⟨_, hne, hsupp, hp, hind, hend⟩ := Finset.mem_filter.mp ha
  constructor
  · intro h
    have he := (Finset.mem_filter.mp h).2.2.2.2.1 ⟨1, by omega⟩ (by omega) (by omega)
    rcases he with h | h
    · exact (Finset.notMem_erase _ _ h).elim
    · rw [succ_one hn] at h
      exact (Finset.mem_erase.mp h).2
  · intro h2
    have herne : (a.erase (s ⟨1, by omega⟩)).Nonempty := by
      have he := hind ⟨3, by omega⟩ (by omega) (by omega)
      rcases he with h3 | h4
      · exact ⟨s ⟨3, by omega⟩, Finset.mem_erase.mpr ⟨label_ne s _ _ (by dsimp; omega), h3⟩⟩
      · refine ⟨s (successor (show 0 < n by omega) ⟨3, by omega⟩),
          Finset.mem_erase.mpr ⟨?_, h4⟩⟩
        apply label_ne
        rw [succ_val _ (by omega)]
        dsimp
        omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, herne,
      (Finset.erase_subset _ _).trans hsupp,
      fun h => hp ((Finset.mem_erase.mp h).2), ?_, Or.inl (Finset.notMem_erase _ _)⟩
    intro i hi hib
    by_cases hi1 : i.val = 1
    · right
      have he : i = (⟨1, by omega⟩ : Fin n) := Fin.ext hi1
      rw [he, succ_one hn]
      exact Finset.mem_erase.mpr ⟨label_ne s _ _ (by dsimp; omega), h2⟩
    · rcases hind i hi hib with h | h
      · exact Or.inl (Finset.mem_erase.mpr ⟨label_ne s _ _ (by dsimp; omega), h⟩)
      · right
        refine Finset.mem_erase.mpr ⟨label_ne s _ _ ?_, h⟩
        rw [succ_val _ hib]
        dsimp
        omega

/-- Actual original s2 round; both families retain the original ground V. -/
theorem second_round {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :
    remaining (tailFaces (by omega) s) (s ⟨1, by omega⟩) = branchA hn s ∪ branchB hn s := by
  ext a
  simp only [mem_remaining, branchA, branchB, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hnflip⟩
    by_cases h1 : s ⟨1, by omega⟩ ∈ a
    · right
      refine ⟨ha, h1, ?_⟩
      intro h2
      apply hnflip
      simpa only [flip, if_pos h1] using (tail_erase_iff hn s a ha).mpr h2
    · left
      refine ⟨ha, h1, ?_⟩
      by_contra hl
      apply hnflip
      simpa only [flip, if_neg h1] using (tail_insert_iff hn s a ha).mpr hl
  · rintro (⟨ha, h1, hl⟩ | ⟨ha, h1, h2⟩)
    · refine ⟨ha, ?_⟩
      rw [flip, if_neg h1]
      exact fun h => (tail_insert_iff hn s a ha).mp h hl
    · refine ⟨ha, ?_⟩
      rw [flip, if_pos h1]
      exact fun h => h2 ((tail_erase_iff hn s a ha).mp h)

theorem second_original {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :
    remaining (remaining (FiniteVertexDominationCollapse.faceSet
      (noncover (show 0 < n by omega) s)) (point (by omega) s)) (s ⟨1, by omega⟩) =
      insert {point (by omega) s} (branchA hn s ∪ branchB hn s) := by
  rw [first_round]
  have hpw : point (show 3 ≤ n by omega) s ≠ s ⟨1, by omega⟩ :=
    label_ne s _ _ (by dsimp [pointIndex]; omega)
  have hsingle : remaining ({{point (show 3 ≤ n by omega) s}} : Finset (Finset V))
      (s ⟨1, by omega⟩) = {{point (by omega) s}} := by
    apply remaining_of_fixed
    right
    intro a ha
    have he : a = {point (by omega) s} := Finset.mem_singleton.mp ha
    simp [he, Ne.symm hpw]
  have h := survivors_by_pin (tailFaces (show 3 ≤ n by omega) s)
    {{point (by omega) s}} [s ⟨1, by omega⟩] (point (by omega) s)
    (fun a ha => tail_omits_point (by omega) s ha)
    (by intro a ha; have he := Finset.mem_singleton.mp ha; simp [he])
    (by simpa using hpw)
  simpa only [survivors, Finset.union_singleton, hsingle, second_round] using h

/-- The actual A pins: y2=1, y3=0, yn=0. -/
theorem branchA_fixed {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V)
    {a : Finset V} (ha : a ∈ branchA hn s) :
    point (by omega) s ∉ a ∧ s ⟨1, by omega⟩ ∉ a ∧
      s ⟨2, by omega⟩ ∈ a ∧ s ⟨n-1, by omega⟩ ∈ a := by
  obtain ⟨ht, h1, hl⟩ := Finset.mem_filter.mp ha
  have he := (Finset.mem_filter.mp ht).2.2.2.2.1 ⟨1, by omega⟩ (by omega) (by omega)
  rw [succ_one hn] at he
  exact ⟨tail_omits_point (by omega) s ht, h1, he.resolve_left h1, hl⟩

/-- The actual B pins: yn=y3=1, y2=y4=y(n-1)=0. -/
theorem branchB_fixed {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V)
    {a : Finset V} (ha : a ∈ branchB hn s) :
    point (by omega) s ∉ a ∧ s ⟨n-1, by omega⟩ ∉ a ∧ s ⟨2, by omega⟩ ∉ a ∧
      s ⟨1, by omega⟩ ∈ a ∧ s ⟨3, by omega⟩ ∈ a ∧ s ⟨n-2, by omega⟩ ∈ a := by
  obtain ⟨ht, h1, h2⟩ := Finset.mem_filter.mp ha
  obtain ⟨_, _, _, hp, hind, hend⟩ := Finset.mem_filter.mp ht
  have hl : s ⟨n-1, by omega⟩ ∉ a := hend.resolve_left (not_not.mpr h1)
  have h3 : s ⟨3, by omega⟩ ∈ a := by
    have he := hind ⟨2, by omega⟩ (by omega) (by omega)
    have hs : successor (show 0 < n by omega) ⟨2, by omega⟩ =
        (⟨3, by omega⟩ : Fin n) := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [hs] at he
    exact he.resolve_left h2
  have hprev : s ⟨n-2, by omega⟩ ∈ a := by
    have he := hind ⟨n-2, by omega⟩ (by omega) (by omega)
    have hs : successor (show 0 < n by omega) ⟨n-2, by omega⟩ =
        (⟨n-1, by omega⟩ : Fin n) := by
      apply Fin.ext
      rw [succ_val _ (by omega)]
      dsimp
      omega
    rw [hs] at he
    exact he.resolve_right hl
  exact ⟨hp, hl, h2, h1, h3, hprev⟩

/-- Independence of the complement on the half-open original-index interval.
Here lo/hi are zero based and all constraints use the original successor. -/
def IntervalIndependent {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V)
    (lo hi : Nat) (a : Finset V) : Prop :=
  ∀ i : Fin n, lo ≤ i.val → i.val+1 < hi →
    s i ∈ a ∨ s (successor (show 0 < n by omega) i) ∈ a

/-- EXACT A family: the free independent-complement interval is 4,...,n-1
in one-based notation, with no other constraints on its internal faces. -/
theorem branchA_iff {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (a : Finset V) :
    a ∈ branchA hn s ↔ a ⊆ ground s ∧ point (by omega) s ∉ a ∧
      s ⟨1, by omega⟩ ∉ a ∧ s ⟨2, by omega⟩ ∈ a ∧ s ⟨n-1, by omega⟩ ∈ a ∧
        IntervalIndependent hn s 3 (n-1) a := by
  constructor
  · intro ha
    obtain ⟨hp, h1, h2, hl⟩ := branchA_fixed hn s ha
    have ht := (Finset.mem_filter.mp ha).1
    obtain ⟨_, hne, hsupp, _, hind, _⟩ := Finset.mem_filter.mp ht
    exact ⟨hsupp, hp, h1, h2, hl, fun i hi hib => hind i (by omega) (by omega)⟩
  · rintro ⟨hsupp, hp, h1, h2, hl, hI⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s ⟨2, by omega⟩, h2⟩,
      hsupp, hp, ?_, Or.inl h1⟩, h1, hl⟩
    intro i hi hib
    by_cases hi1 : i.val = 1
    · right
      have he : successor (show 0 < n by omega) i = (⟨2, by omega⟩ : Fin n) := by
        apply Fin.ext
        rw [succ_val _ hib]
        dsimp
        omega
      simpa only [he] using h2
    · by_cases hi2 : i.val = 2
      · left
        have he : i = (⟨2, by omega⟩ : Fin n) := Fin.ext hi2
        simpa only [he] using h2
      · by_cases hil : i.val+1 = n-1
        · right
          have he : successor (show 0 < n by omega) i = (⟨n-1, by omega⟩ : Fin n) := by
            apply Fin.ext
            rw [succ_val _ hib]
            exact hil
          simpa only [he] using hl
        · exact hI i (by omega) (by omega)

/-- EXACT B family: the free independent-complement interval is 5,...,n-2.
For n=6 it is the empty augmented path, not the empty family. -/
theorem branchB_iff {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (a : Finset V) :
    a ∈ branchB hn s ↔ a ⊆ ground s ∧ point (by omega) s ∉ a ∧
      s ⟨n-1, by omega⟩ ∉ a ∧ s ⟨2, by omega⟩ ∉ a ∧ s ⟨1, by omega⟩ ∈ a ∧
        s ⟨3, by omega⟩ ∈ a ∧ s ⟨n-2, by omega⟩ ∈ a ∧
          IntervalIndependent hn s 4 (n-2) a := by
  constructor
  · intro ha
    obtain ⟨hp, hl, h2, h1, h3, hprev⟩ := branchB_fixed hn s ha
    have ht := (Finset.mem_filter.mp ha).1
    obtain ⟨_, hne, hsupp, _, hind, _⟩ := Finset.mem_filter.mp ht
    exact ⟨hsupp, hp, hl, h2, h1, h3, hprev,
      fun i hi hib => hind i (by omega) (by omega)⟩
  · rintro ⟨hsupp, hp, hl, h2, h1, h3, hprev, hI⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s ⟨1, by omega⟩, h1⟩,
      hsupp, hp, ?_, Or.inr hl⟩, h1, h2⟩
    intro i hi hib
    by_cases hi1 : i.val = 1
    · left
      have he : i = (⟨1, by omega⟩ : Fin n) := Fin.ext hi1
      simpa only [he] using h1
    · by_cases hi2 : i.val = 2
      · right
        have he : successor (show 0 < n by omega) i = (⟨3, by omega⟩ : Fin n) := by
          apply Fin.ext
          rw [succ_val _ hib]
          dsimp
          omega
        simpa only [he] using h3
      · by_cases hi3 : i.val = 3
        · left
          have he : i = (⟨3, by omega⟩ : Fin n) := Fin.ext hi3
          simpa only [he] using h3
        · by_cases hil : i.val = n-2
          · left
            have he : i = (⟨n-2, by omega⟩ : Fin n) := Fin.ext hil
            simpa only [he] using hprev
          · by_cases hip : i.val+1 = n-2
            · right
              have he : successor (show 0 < n by omega) i = (⟨n-2, by omega⟩ : Fin n) := by
                apply Fin.ext
                rw [succ_val _ hib]
                exact hip
              simpa only [he] using hprev
            · exact hI i (by omega) (by omega)

private theorem noBranch_remaining (R : RelativeFamily (V := V)) (v : V) :
    (R.noBranch v).F = (remaining R.F v).filter (fun a => v ∉ a) := by
  rw [RelativeFamily.noBranch_faces, R.remaining_eq]
  ext a
  simp only [Finset.mem_filter, Finset.mem_union, RelativeFamily.mem_A, RelativeFamily.mem_B]
  tauto

private theorem yesBranch_remaining (R : RelativeFamily (V := V)) (v : V) :
    (R.yesBranch v).F = (remaining R.F v).filter (fun a => v ∈ a) := by
  rw [RelativeFamily.yesBranch_faces, R.remaining_eq]
  ext a
  simp only [Finset.mem_filter, Finset.mem_union, RelativeFamily.mem_A, RelativeFamily.mem_B]
  tauto

theorem second_noBranch_faces {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :
    (((nativeRelative (noncover (show 0 < n by omega) s)).noBranch
      (point (by omega) s)).noBranch (s ⟨1, by omega⟩)).F = branchA hn s := by
  rw [noBranch_remaining, first_noBranch_faces, second_round]
  ext a
  simp only [Finset.mem_filter, Finset.mem_union, branchA, branchB]
  simp only [Finset.mem_filter]
  tauto

theorem second_yesBranch_faces {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :
    (((nativeRelative (noncover (show 0 < n by omega) s)).noBranch
      (point (by omega) s)).yesBranch (s ⟨1, by omega⟩)).F = branchB hn s := by
  rw [yesBranch_remaining, first_noBranch_faces, second_round]
  ext a
  simp only [Finset.mem_filter, Finset.mem_union, branchA, branchB]
  simp only [Finset.mem_filter]
  tauto

/-- Every later round at a coordinate other than original s2 restricts to
these two actual branches. This is equality of greedy survivors, not counts. -/
theorem branch_survivors {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (vs : List V)
    (hvs : s ⟨1, by omega⟩ ∉ vs) :
    survivors (remaining (tailFaces (by omega) s) (s ⟨1, by omega⟩)) vs =
      survivors (branchA hn s) vs ∪ survivors (branchB hn s) vs := by
  rw [second_round]
  exact survivors_by_pin _ _ vs (s ⟨1, by omega⟩)
    (fun a ha => (Finset.mem_filter.mp ha).2.1)
    (fun a ha => (Finset.mem_filter.mp ha).2.1) hvs

end D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches
