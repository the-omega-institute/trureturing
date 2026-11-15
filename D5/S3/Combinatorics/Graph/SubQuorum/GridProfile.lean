/- GID: D5/S3/Combinatorics/Graph/SubQuorum/GridProfile
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/GridProfile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact independent-path neighborhood defects for grid row profiles. -/

import D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

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
        change i-3=j-3 at he
        omega
      have hs : L.card+U.card=P.card := by
        simpa only [L,U,not_lt] using Finset.card_filter_add_card_filter_not (s:=P) (· < 3)
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

/-- The local adjacent-row condition retains its sole positive exception. -/
def Compatible {n : ℕ} (a : Fin n → ℤ) : Prop :=
  ∀ i j, (SimpleGraph.pathGraph n).Adj i j → a i+a j ≤ 0 ∨ (a i=1 ∧ a j=1)

def upperLevel {n : ℕ} (a : Fin n → ℤ) (h : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 2*(h : ℤ)+3 ≤ a i)

def lowerLevel {n : ℕ} (a : Fin n → ℤ) (h : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a i ≤ -(2*(h : ℤ)+3))

private theorem level_neighbors {n : ℕ} (a : Fin n → ℤ) (ha : Compatible a) (h : ℕ) :
    neighbors (upperLevel a h) ⊆ lowerLevel a h := by
  intro i hi
  obtain ⟨j,hj,hji⟩ := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  rcases ha j i hji with hs | he
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  · omega

private theorem level_independent {n : ℕ} (a : Fin n → ℤ) (ha : Compatible a) (h : ℕ) :
    ∀ i ∈ upperLevel a h, ∀ j ∈ upperLevel a h,
      ¬ (SimpleGraph.pathGraph n).Adj i j := by
  intro i hi j hj hij
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  rcases ha i j hij with hs | he <;> omega

/-- Every even-order profile level has a nonpositive signed count. -/
theorem even_level_balance {n : ℕ} (hn : n % 2 = 0)
    (a : Fin n → ℤ) (ha : Compatible a) (h : ℕ) :
    (upperLevel a h).card ≤ (lowerLevel a h).card :=
  (even_path_expansion hn _).trans (Finset.card_le_card (level_neighbors a ha h))

/-- Every odd-order level has signed count at most one. -/
theorem odd_level_balance {n : ℕ} (hn : n % 2 = 1)
    (a : Fin n → ℤ) (ha : Compatible a) (h : ℕ) :
    (upperLevel a h).card ≤ (lowerLevel a h).card+1 := by
  have hh := odd_path_defect_bound hn (upperLevel a h)
  have hc := Finset.card_le_card (level_neighbors a ha h)
  omega

/-- A positive level imbalance fixes the complete sign sequence, not only its count. -/
theorem positive_level_forces_alternation {n : ℕ} (hn : n % 2 = 1)
    (a : Fin n → ℤ) (ha : Compatible a) (h : ℕ)
    (hpos : (lowerLevel a h).card < (upperLevel a h).card) :
    ∀ i : Fin n, (i.val % 2 = 0 → 0<a i) ∧ (i.val % 2 = 1 → a i<0) := by
  have hc := Finset.card_le_card (level_neighbors a ha h)
  have hd : (neighbors (upperLevel a h)).card < (upperLevel a h).card := by omega
  have hs := odd_path_defect_support hn (upperLevel a h) (level_independent a ha h) hd
  intro i
  constructor
  · intro hi
    have hm := (hs i).mpr hi
    have hv := (Finset.mem_filter.mp hm).2
    omega
  · intro hi
    have hiv : (0 : ℕ) < (i : Fin n).val := by omega
    let j : Fin n := ⟨i.val-1,by omega⟩
    have hj : j.val % 2=0 := by dsimp [j]; omega
    have hjm := (hs j).mpr hj
    have hjv := (Finset.mem_filter.mp hjm).2
    have he : (SimpleGraph.pathGraph n).Adj j i :=
      SimpleGraph.pathGraph_adj.mpr (Or.inl (by dsimp [j]; omega))
    have him : i ∈ lowerLevel a h := level_neighbors a ha h
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hjm,he⟩)
    have hiv' := (Finset.mem_filter.mp him).2
    omega

private theorem threshold_sum (H r : ℕ) (hr : r ≤ H) :
    (∑ h ∈ Finset.range H, if h<r then (1 : ℤ) else 0) = r := by
  rw [← Finset.sum_filter]
  have he : (Finset.range H).filter (· < r) = Finset.range r := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [he]
  simp

private theorem odd_level_identity (H : ℕ) (x : ℤ) (hx : x%2=1)
    (hlo : -(2*(H : ℤ)+1) ≤ x) (hhi : x ≤ 2*(H : ℤ)+1) :
    x = (if 0<x then 1 else -1) + 2 *
      ((∑ h ∈ Finset.range H, if 2*(h : ℤ)+3 ≤ x then (1 : ℤ) else 0) -
       (∑ h ∈ Finset.range H, if x ≤ -(2*(h : ℤ)+3) then (1 : ℤ) else 0)) := by
  by_cases hp : 0<x
  · let r := ((x-1)/2).toNat
    have hr : 2*(r : ℤ)+1=x := by dsimp [r]; omega
    have hrH : r≤H := by omega
    have hpos : (∑ h ∈ Finset.range H, if 2*(h : ℤ)+3 ≤ x then (1 : ℤ) else 0) = r := by
      have he (h : ℕ) : 2*(h : ℤ)+3 ≤ x ↔ h<r := by omega
      simp_rw [he]
      exact threshold_sum H r hrH
    have hneg : (∑ h ∈ Finset.range H, if x ≤ -(2*(h : ℤ)+3) then (1 : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro h hh
      have he : ¬ x ≤ -(2*(h : ℤ)+3) := by omega
      exact ite_eq_right he
    rw [ite_eq_left hp,hpos,hneg]
    omega
  · let r := ((-x-1)/2).toNat
    have hr : 2*(r : ℤ)+1= -x := by dsimp [r]; omega
    have hrH : r≤H := by omega
    have hpos : (∑ h ∈ Finset.range H, if 2*(h : ℤ)+3 ≤ x then (1 : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro h hh
      have he : ¬ 2*(h : ℤ)+3 ≤ x := by omega
      simp [he]
    have hneg : (∑ h ∈ Finset.range H, if x ≤ -(2*(h : ℤ)+3) then (1 : ℤ) else 0) = r := by
      have he (h : ℕ) : x ≤ -(2*(h : ℤ)+3) ↔ h<r := by omega
      simp_rw [he]
      exact threshold_sum H r hrH
    rw [ite_eq_right hp,hpos,hneg]
    omega

/-- Finite level decomposition includes every negative entry, without a fixed lower bound. -/
theorem profile_level_identity {n : ℕ} (a : Fin n → ℤ) (H : ℕ)
    (hodd : ∀ i, a i%2=1)
    (hlo : ∀ i, -(2*(H : ℤ)+1) ≤ a i) (hhi : ∀ i, a i ≤ 2*(H : ℤ)+1) :
    (∑ i, a i) = (∑ i, if 0<a i then (1 : ℤ) else -1) +
      2 * ∑ h ∈ Finset.range H,
        ((upperLevel a h).card - ((lowerLevel a h).card : ℤ)) := by
  have hpoint := fun i => odd_level_identity H (a i) (hodd i) (hlo i) (hhi i)
  have hp (h : ℕ) : (∑ i, if 2*(h : ℤ)+3 ≤ a i then (1 : ℤ) else 0) =
      (upperLevel a h).card := by
    simp only [upperLevel,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hm (h : ℕ) : (∑ i, if a i ≤ -(2*(h : ℤ)+3) then (1 : ℤ) else 0) =
      (lowerLevel a h).card := by
    simp only [lowerLevel,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hpall : (∑ i, ∑ h ∈ Finset.range H,
      if 2*(h : ℤ)+3 ≤ a i then (1 : ℤ) else 0) =
      ∑ h ∈ Finset.range H, ((upperLevel a h).card : ℤ) := by
    rw [Finset.sum_comm]
    simp_rw [hp]
  have hmall : (∑ i, ∑ h ∈ Finset.range H,
      if a i ≤ -(2*(h : ℤ)+3) then (1 : ℤ) else 0) =
      ∑ h ∈ Finset.range H, ((lowerLevel a h).card : ℤ) := by
    rw [Finset.sum_comm]
    simp_rw [hm]
  conv_lhs => arg 2; ext i; rw [hpoint i]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,
    hpall,hmall,Finset.sum_sub_distrib]

private theorem sign_sum_count {n : ℕ} (a : Fin n → ℤ) :
    (∑ i, if 0<a i then (1 : ℤ) else -1) =
      2*((Finset.univ.filter (fun i => 0<a i)).card : ℤ)-n := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i => 0<a i)
  have hs : (∑ i, if 0<a i then (1 : ℤ) else -1) =
      ((Finset.univ.filter (fun i => 0<a i)).card : ℤ) -
        ((Finset.univ.filter (fun i => ¬ 0<a i)).card : ℤ) := by
    simp [Finset.sum_ite,sub_eq_add_neg]
  rw [hs]
  simp only [Finset.card_univ,Fintype.card_fin] at hc
  omega

/-- The no-three-positive rule bounds the actual sign sum, including both end remainders. -/
theorem sign_sum_bound {n : ℕ} (a : Fin n → ℤ)
    (hthree : ∀ i j k : Fin n, i.val+1=j.val → j.val+1=k.val →
      ¬ (0<a i ∧ 0<a j ∧ 0<a k)) :
    (∑ i, if 0<a i then (1 : ℤ) else -1) ≤ (n : ℤ)-2*(n/3 : ℕ) := by
  classical
  let P := Finset.univ.filter (fun i => 0<a i)
  let Q := P.image Fin.val
  have hb : Q.card ≤ n-n/3 := by
    apply three_free_card n Q
    · intro i hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact j.isLt
    · rintro i ⟨h0,h1,h2⟩
      obtain ⟨j,hj,hej⟩ := Finset.mem_image.mp h0
      obtain ⟨k,hk,hek⟩ := Finset.mem_image.mp h1
      obtain ⟨l,hl,hel⟩ := Finset.mem_image.mp h2
      exact hthree j k l (by omega) (by omega)
        ⟨(Finset.mem_filter.mp hj).2,(Finset.mem_filter.mp hk).2,(Finset.mem_filter.mp hl).2⟩
  have hc : Q.card=P.card := Finset.card_image_of_injective _ Fin.val_injective
  rw [hc] at hb
  rw [sign_sum_count]
  change 2*(P.card : ℤ)-n ≤ _
  omega

private theorem alternating_sign_sum (n : ℕ) :
    (∑ i : Fin n, if i.val%2=0 then (1 : ℤ) else -1) = (n%2 : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih]
    split_ifs <;> omega

private theorem threshold_sum_le (H r : ℕ) :
    (∑ h ∈ Finset.range H, if h<r then (1 : ℤ) else 0) ≤ r := by
  rw [← Finset.sum_filter]
  have hs : (Finset.range H).filter (· < r) ⊆ Finset.range r := by
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  have hc := Finset.card_le_card hs
  simp only [Finset.card_range] at hc
  simpa using (show (((Finset.range H).filter (· < r)).card : ℤ) ≤ r by omega)

/-- The source odd-integer row-profile theorem, with no bound on negative entries. -/
theorem profile_bound {n : ℕ} (a : Fin n → ℤ) (A : ℕ) (hA : A%2=1)
    (hodd : ∀ i, a i%2=1) (hupper : ∀ i, a i ≤ A) (ha : Compatible a)
    (hthree : ∀ i j k : Fin n, i.val+1=j.val → j.val+1=k.val →
      ¬ (0<a i ∧ 0<a j ∧ 0<a k)) :
    (∑ i, a i) ≤ if n%2=0 then (n : ℤ)-2*(n/3 : ℕ)
      else max (A : ℤ) ((n : ℤ)-2*(n/3 : ℕ)) := by
  classical
  let H := ∑ i, (a i).natAbs
  have habs (i : Fin n) : |a i| ≤ (H : ℤ) := by
    have hi : (a i).natAbs ≤ H := by
      change (a i).natAbs ≤ ∑ j, (a j).natAbs
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j).natAbs) (Finset.mem_univ i)
    rw [← Int.natCast_natAbs]
    exact_mod_cast hi
  have hlo (i : Fin n) : -(2*(H : ℤ)+1) ≤ a i := by
    have hi := (abs_le.mp (habs i)).1
    omega
  have hhi (i : Fin n) : a i ≤ 2*(H : ℤ)+1 := by
    have hi := (abs_le.mp (habs i)).2
    omega
  have hid := profile_level_identity a H hodd hlo hhi
  let diff : ℕ → ℤ := fun h => (upperLevel a h).card-((lowerLevel a h).card : ℤ)
  change (∑ i, a i) = _+2*∑ h ∈ Finset.range H, diff h at hid
  by_cases hn : n%2=0
  · have hd : (∑ h ∈ Finset.range H, diff h) ≤ 0 := by
      apply Finset.sum_nonpos
      intro h hh
      have hc := even_level_balance hn a ha h
      dsimp [diff]
      omega
    rw [ite_eq_left hn]
    have hs := sign_sum_bound a hthree
    omega
  · have hno : n%2=1 := by omega
    rw [ite_eq_right hn]
    by_cases hp : ∃ h ∈ Finset.range H, (lowerLevel a h).card < (upperLevel a h).card
    · obtain ⟨h,hh,hpos⟩ := hp
      have halt := positive_level_forces_alternation hno a ha h hpos
      have hs : (∑ i, if 0<a i then (1 : ℤ) else -1)=1 := by
        calc
          _ = ∑ i : Fin n, if i.val%2=0 then (1 : ℤ) else -1 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases he : i.val%2=0
            · simp [he,(halt i).1 he]
            · have ho : i.val%2=1 := by omega
              have hv := (halt i).2 ho
              simp [he,show ¬ 0<a i by omega]
          _ = 1 := by rw [alternating_sign_sum,hno]; norm_num
      have hd : (∑ h ∈ Finset.range H, diff h) ≤ A/2 := by
        calc
          _ ≤ ∑ h ∈ Finset.range H, if h<A/2 then (1 : ℤ) else 0 := by
            apply Finset.sum_le_sum
            intro h hh
            by_cases he : h<A/2
            · rw [ite_eq_left he]
              have hc := odd_level_balance hno a ha h
              dsimp [diff]
              omega
            · rw [ite_eq_right he]
              have hempty : upperLevel a h=∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro i hi
                have hc := (Finset.mem_filter.mp hi).2
                have hu := hupper i
                omega
              simp [diff,hempty]
          _ ≤ _ := threshold_sum_le H (A/2)
      have hA' : (A : ℤ)=1+2*(A/2 : ℕ) := by omega
      have hb : (∑ i, a i) ≤ A := by omega
      exact hb.trans (le_max_left _ _)
    · have hd : (∑ h ∈ Finset.range H, diff h) ≤ 0 := by
        apply Finset.sum_nonpos
        intro h hh
        have hc : (upperLevel a h).card ≤ (lowerLevel a h).card := by
          by_contra hc
          exact hp ⟨h,hh,by omega⟩
        dsimp [diff]
        omega
      have hs := sign_sum_bound a hthree
      have hb : (∑ i, a i) ≤ (n : ℤ)-2*(n/3 : ℕ) := by omega
      exact hb.trans (le_max_right _ _)

/-- Pairing an odd path around any even-indexed pivot preserves the endpoint term. -/
theorem odd_adjacent_sum_bound {n : ℕ} (hn : n%2=1) (f : Fin n → ℤ)
    (hf : ∀ i j, (SimpleGraph.pathGraph n).Adj i j → f i+f j ≤ 2)
    (pivot : Fin n) (hp : pivot.val%2=0) :
    (∑ i, f i) ≤ (n : ℤ)-1+f pivot := by
  let m := mate hn pivot hp
  have hm : Function.Involutive m := mate_involutive hn pivot hp
  have hs : (∑ i, f (m i)) = ∑ i, f i :=
    Function.Bijective.sum_comp ⟨hm.injective,hm.surjective⟩ f
  have hb : (∑ i, (f i+f (m i))) ≤
      ∑ i, (2+(if i=pivot then 2*f pivot-2 else 0)) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases he : i=pivot
    · subst i
      simp [m,mate]
      omega
    · have hh := hf i (m i) (mate_adj hn pivot hp i he)
      simpa [he] using hh
  rw [Finset.sum_add_distrib,hs] at hb
  have hr : (∑ i : Fin n, (2+(if i=pivot then 2*f pivot-2 else 0))) =
      2*(n : ℤ)+2*f pivot-2 := by simp [Finset.sum_add_distrib]; ring
  rw [hr] at hb
  omega

/-- Pairing an even path leaves no endpoint term. -/
theorem even_adjacent_sum_bound {n : ℕ} (hn : n%2=0) (f : Fin n → ℤ)
    (hf : ∀ i j, (SimpleGraph.pathGraph n).Adj i j → f i+f j ≤ 2) :
    (∑ i, f i) ≤ n := by
  let m : Fin n → Fin n := fun i => ⟨pairIndex i.val,(pairIndex_facts n i.val hn i.isLt).1⟩
  have hm : Function.Involutive m := by
    intro i
    apply Fin.ext
    exact (pairIndex_facts n i.val hn i.isLt).2.2
  have hs : (∑ i, f (m i)) = ∑ i, f i :=
    Function.Bijective.sum_comp ⟨hm.injective,hm.surjective⟩ f
  have hb : (∑ i, (f i+f (m i))) ≤ ∑ _i : Fin n, (2 : ℤ) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hf i (m i) (SimpleGraph.pathGraph_adj.mpr (pairIndex_facts n i.val hn i.isLt).2.1)
  rw [Finset.sum_add_distrib,hs] at hb
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  omega

/-- At the odd ladder upper bound every even column is full and every odd column empty. -/
theorem odd_ladder_rigidity {n : ℕ} (hn : n%2=1) (c : Fin n → ℕ)
    (hcap : ∀ i, c i≤2)
    (hpair : ∀ i j, (SimpleGraph.pathGraph n).Adj i j → c i+c j≤2)
    (htotal : n+1 ≤ ∑ i, c i) :
    ∀ i, c i=if i.val%2=0 then 2 else 0 := by
  have heven (i : Fin n) (hi : i.val%2=0) : c i=2 := by
    have hb := odd_adjacent_sum_bound hn (fun j => (c j : ℤ))
      (fun j k hjk => by have hh := hpair j k hjk; exact_mod_cast hh) i hi
    rw [← Nat.cast_sum] at hb
    have hc := hcap i
    omega
  intro i
  by_cases hi : i.val%2=0
  · rw [ite_eq_left hi]
    exact heven i hi
  · have hiv : (0 : ℕ) < (i : Fin n).val := by omega
    let j : Fin n := ⟨i.val-1,by omega⟩
    have hj : j.val%2=0 := by dsimp [j]; omega
    have he := heven j hj
    have hb := hpair j i (SimpleGraph.pathGraph_adj.mpr (Or.inl (by dsimp [j]; omega)))
    rw [ite_eq_right hi]
    omega

end D5.S3.Combinatorics.Graph.SubQuorum.GridProfile
