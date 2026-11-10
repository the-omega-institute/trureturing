/- GID: D5/S3/Combinatorics/Graph/SubQuorum/GridProfile
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/GridProfile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives]
   utility: none
   digest: Exact independent-path neighborhood defects for grid row profiles. -/

import D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-! The path-neighborhood argument of GRID_PROFILE_PROOF, received from
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. A matching leaving an arbitrary even-indexed vertex uncovered
proves the exact exceptional support. Indices here start at zero. -/

namespace D5.S3.Combinatorics.Graph.SubQuorum.GridProfile
open scoped BigOperators

/-- The path row bound counts every final incomplete triple exactly. -/
theorem three_free_card (n : ℕ) (P : Finset ℕ) (hP : ∀ i ∈ P, i < n)
    (hthree : ∀ i, ¬ (i ∈ P ∧ i+1 ∈ P ∧ i+2 ∈ P)) :
    P.card ≤ n-n/3 := by
  classical
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hn : n < 3
    · have hs : P ⊆ Finset.range n := fun i hi => Finset.mem_range.mpr (hP i hi)
      have hc := Finset.card_le_card hs
      simp only [Finset.card_range] at hc
      have hd : n/3=0 := Nat.div_eq_of_lt hn
      omega
    · let L := P.filter (· < 3)
      let U := P.filter (3 ≤ ·)
      let Q := U.image (fun i => i-3)
      have hl : L.card ≤ 2 := by
        have hs : L ⊆ ({0,1,2} : Finset ℕ) := by
          intro i hi
          have hv := (Finset.mem_filter.mp hi).2
          simp only [Finset.mem_insert,Finset.mem_singleton]
          omega
        have hc := Finset.card_le_card hs
        have ht : ({0,1,2} : Finset ℕ).card=3 := by decide
        rw [ht] at hc
        by_contra he
        have heq : L=({0,1,2} : Finset ℕ) := Finset.eq_of_subset_of_card_le hs (by omega)
        have hi (i : ℕ) (hi : i ∈ ({0,1,2} : Finset ℕ)) : i ∈ P :=
          (Finset.mem_filter.mp (heq ▸ hi)).1
        exact hthree 0 ⟨hi 0 (by simp),hi 1 (by simp),hi 2 (by simp)⟩
      have hq : ∀ i ∈ Q, i < n-3 := by
        intro i hi
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
        have hv := Finset.mem_filter.mp hj
        have hjn := hP j hv.1
        omega
      have hqt : ∀ i, ¬ (i ∈ Q ∧ i+1 ∈ Q ∧ i+2 ∈ Q) := by
        rintro i ⟨h0,h1,h2⟩
        have hh (j : ℕ) (hj : j ∈ Q) : j+3 ∈ P := by
          obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hj
          have hv := Finset.mem_filter.mp hk
          have he' : j+3=k := by omega
          exact he' ▸ hv.1
        exact hthree (i+3) ⟨hh i h0,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh (i+1) h1,
          by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh (i+2) h2⟩
      have hb := ih (n-3) (by omega) Q hq hqt
      have hcard : Q.card=U.card := by
        apply Finset.card_image_of_injOn
        intro i hi j hj he
        have hi3 := (Finset.mem_filter.mp hi).2
        have hj3 := (Finset.mem_filter.mp hj).2
        omega
      have hs : L.card+U.card=P.card := by
        simpa only [L,U,not_lt] using Finset.filter_card_add_filter_neg_card_eq_card (s:=P) (· < 3)
      rw [hcard] at hb
      omega

private def mateIndex (pivot i : ℕ) : ℕ :=
  if i < pivot then if i % 2 = 0 then i + 1 else i - 1
  else if i % 2 = 0 then i - 1 else i + 1

private theorem mateIndex_facts (n pivot i : ℕ) (hn : n % 2 = 1)
    (hp : pivot < n) (hpe : pivot % 2 = 0) (hi : i < n) (hne : i ≠ pivot) :
    mateIndex pivot i < n ∧ mateIndex pivot i ≠ pivot ∧
    (i + 1 = mateIndex pivot i ∨ mateIndex pivot i + 1 = i) ∧
    mateIndex pivot (mateIndex pivot i) = i := by
  unfold mateIndex
  split_ifs <;> omega

private def mate {n : ℕ} (hn : n % 2 = 1) (pivot : Fin n)
    (hp : pivot.val % 2 = 0) (i : Fin n) : Fin n :=
  if h : i = pivot then pivot else
    ⟨mateIndex pivot.val i.val,
      (mateIndex_facts n pivot.val i.val hn pivot.isLt hp i.isLt
        (fun he => h (Fin.ext he))).1⟩

private theorem mate_involutive {n : ℕ} (hn : n % 2 = 1) (pivot : Fin n)
    (hp : pivot.val % 2 = 0) : Function.Involutive (mate hn pivot hp) := by
  intro i
  by_cases he : i = pivot
  · subst i; simp [mate]
  · have hf := mateIndex_facts n pivot.val i.val hn pivot.isLt hp i.isLt
      (fun h => he (Fin.ext h))
    have hm : mate hn pivot hp i ≠ pivot := by
      intro h
      have hv := congrArg Fin.val h
      simp only [mate,dite_eq_right he] at hv
      exact hf.2.1 hv
    rw [mate, dite_eq_right hm]
    apply Fin.ext
    simpa only [mate, dite_eq_right he] using hf.2.2.2

private theorem mate_adj {n : ℕ} (hn : n % 2 = 1) (pivot : Fin n)
    (hp : pivot.val % 2 = 0) (i : Fin n) (hi : i ≠ pivot) :
    (SimpleGraph.pathGraph n).Adj i (mate hn pivot hp i) := by
  rw [SimpleGraph.pathGraph_adj]
  simpa only [mate,dite_eq_right hi] using
    (mateIndex_facts n pivot.val i.val hn pivot.isLt hp i.isLt
      (fun h => hi (Fin.ext h))).2.2.1

/-- The actual open neighborhood of an arbitrary finite path selection. -/
def neighbors {n : ℕ} (P : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ u ∈ P, (SimpleGraph.pathGraph n).Adj u v)

/-- Missing any even-indexed path vertex prevents a positive neighborhood defect. -/
theorem card_le_neighbors_of_missing_even {n : ℕ} (hn : n % 2 = 1)
    (P : Finset (Fin n)) (pivot : Fin n) (hp : pivot.val % 2 = 0)
    (hmissing : pivot ∉ P) : P.card ≤ (neighbors P).card := by
  classical
  apply Finset.card_le_card_of_injOn (mate hn pivot hp)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi,
      mate_adj hn pivot hp i (fun h => hmissing (h ▸ hi))⟩
  · exact (mate_involutive hn pivot hp).injective.injOn

/-- A positive independent-path neighborhood defect has exactly alternating support. -/
theorem odd_path_defect_support {n : ℕ} (hn : n % 2 = 1)
    (P : Finset (Fin n))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ (SimpleGraph.pathGraph n).Adj a b)
    (hdefect : (neighbors P).card < P.card) :
    ∀ i : Fin n, i ∈ P ↔ i.val % 2 = 0 := by
  have hall (i : Fin n) (hi : i.val % 2 = 0) : i ∈ P := by
    by_contra hnot
    have hc := card_le_neighbors_of_missing_even hn P i hi hnot
    omega
  intro i
  constructor
  · intro hi
    by_contra he
    have hv : 0 < i.val := by omega
    let j : Fin n := ⟨i.val-1,by omega⟩
    have hj : j.val % 2 = 0 := by dsimp [j]; omega
    exact hP j (hall j hj) i hi
      (SimpleGraph.pathGraph_adj.mpr (Or.inl (by dsimp [j]; omega)))
  · exact hall i

/-- The exceptional path loses at most one neighbor, including the one-vertex path. -/
theorem odd_path_defect_bound {n : ℕ} (hn : n % 2 = 1)
    (P : Finset (Fin n)) : P.card ≤ (neighbors P).card + 1 := by
  classical
  let pivot : Fin n := ⟨0,by omega⟩
  have he : (P.erase pivot).card ≤ (neighbors P).card := by
    apply Finset.card_le_card_of_injOn (mate hn pivot (by rfl))
    · intro i hi
      have hm := Finset.mem_erase.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hm.2,
        mate_adj hn pivot (by rfl) i hm.1⟩
    · exact (mate_involutive hn pivot (by rfl)).injective.injOn
  by_cases hp : pivot ∈ P
  · rw [Finset.card_erase_of_mem hp] at he
    omega
  · simp only [Finset.erase_eq_of_notMem hp] at he
    omega

private def pairIndex (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

private theorem pairIndex_facts (n i : ℕ) (hn : n % 2 = 0) (hi : i < n) :
    pairIndex i < n ∧ (i + 1 = pairIndex i ∨ pairIndex i + 1 = i) ∧
    pairIndex (pairIndex i) = i := by
  unfold pairIndex
  split_ifs <;> omega

/-- An even path has no positive neighborhood defect, without an independence premise. -/
theorem even_path_expansion {n : ℕ} (hn : n % 2 = 0)
    (P : Finset (Fin n)) : P.card ≤ (neighbors P).card := by
  classical
  let f : Fin n → Fin n := fun i => ⟨pairIndex i.val,(pairIndex_facts n i.val hn i.isLt).1⟩
  have hf : Function.Involutive f := by
    intro i
    apply Fin.ext
    exact (pairIndex_facts n i.val hn i.isLt).2.2
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi,
      SimpleGraph.pathGraph_adj.mpr (pairIndex_facts n i.val hn i.isLt).2.1⟩
  · exact hf.injective.injOn

end D5.S3.Combinatorics.Graph.SubQuorum.GridProfile
