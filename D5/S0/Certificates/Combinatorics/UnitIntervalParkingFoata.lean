/- GID: D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata
   generality: I
   mirror-B: D5/B/S0/Certificates/Combinatorics/UnitIntervalParkingFoata
   mirror-E: none(waiver:general-theorems-only)
   anchors: []
   utility: none
   digest: Parking-process specifications, Foata commutation for distinct-letter and nondecreasing words, and the unit-interval characterisation. -/

import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Unit-interval parking and Foata's transformation

This module proves the first-vacant-spot specification, the local
unit-displacement criterion, and monotonicity of the parking process.
Foata's transformation preserves the multiset of letters, satisfies its
recursive last-letter equation, and fixes nondecreasing words. Parking
commutes with Foata for distinct-letter words and for nondecreasing words.
The unit-interval condition is characterised by the recursive predicate unitRun.

Parking is computed on the unbounded nonnegative street; IsParkingFunction
then requires preferences and final spots to lie in 1 through the word length.
This total extension agrees with finite-street parking whenever all cars park.
The output order is car order. The structural search advances at most as many
times as there are occupied-list entries.

Conjecture 6.3 is not proved. The unrestricted standardization route remains
unproved: identification of parking spots with stable ranks and transport of
equal-occurrence order through the rotations have not been established.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata

private def seek : Nat → List Nat → Nat → Nat
  | 0, _, p => p
  | fuel + 1, occupied, p =>
      if p ∈ occupied then seek fuel occupied (p + 1) else p

/-- First vacant spot at or above the preference. Among length + 1
successive spots at least one is vacant, so length advances suffice. -/
def parkStep (occupied : List Nat) (p : Nat) : Nat :=
  seek occupied.length occupied p

private theorem seek_erase (fuel : Nat) (occupied : List Nat) (p q : Nat) (h : p < q) :
    seek fuel occupied q = seek fuel (occupied.erase p) q := by
  induction fuel generalizing q with
  | zero => rfl
  | succ fuel ih =>
    simp only [seek, List.mem_erase_of_ne (show q ≠ p by omega)]
    split
    · exact ih (q + 1) (by omega)
    · rfl

private theorem parkStep_eq (occupied : List Nat) (p : Nat) :
    parkStep occupied p =
      if p ∈ occupied then parkStep (occupied.erase p) (p + 1) else p := by
  cases occupied with
  | nil => simp [parkStep, seek]
  | cons x xs =>
    simp only [parkStep, List.length_cons, seek]
    split
    · rename_i h
      have hl := List.length_erase_of_mem h
      rw [show ((x :: xs).erase p).length = xs.length by simpa using hl]
      exact seek_erase xs.length (x :: xs) p (p + 1) (by omega)
    · rfl

/-- Parking the remaining cars with the specified occupied spots. -/
def parkFrom (occupied : List Nat) : List Nat → List Nat
  | [] => []
  | p :: a => let q := parkStep occupied p; q :: parkFrom (q :: occupied) a

/-- Final spots, in car order, starting with an empty street. -/
def spots (a : List Nat) : List Nat := parkFrom [] a

/-- Every preference and every final spot belongs to the finite street. -/
def IsParkingFunction (a : List Nat) : Prop :=
  (∀ p ∈ a, 1 ≤ p ∧ p ≤ a.length) ∧
  (∀ q ∈ spots a, 1 ≤ q ∧ q ≤ a.length)

/-- A parking function in which every car moves at most one place. -/
def IsUnitInterval (a : List Nat) : Prop :=
  IsParkingFunction a ∧ (a.zip (spots a)).all (fun pq => pq.2 ≤ pq.1 + 1) = true

/-- Rotate each completed block by moving its last entry to the front.
The accumulator contains the unfinished block, in its original order. -/
def rotateBlocks (cut : Nat → Bool) (pending : List Nat) : List Nat → List Nat
  | [] => pending
  | y :: ys => if cut y then (y :: pending) ++ rotateBlocks cut [] ys
      else rotateBlocks cut (pending ++ [y]) ys

/-- One Foata insertion, selecting cuts from the previous last letter. -/
def foataStep (w : List Nat) (x : Nat) : List Nat :=
  let cut := if w.getLastD x ≤ x then (fun y => decide (y ≤ x))
    else (fun y => decide (x < y))
  rotateBlocks cut [] w ++ [x]

/-- Foata's transformation, processing the input from left to right. -/
def foata (a : List Nat) : List Nat := a.foldl foataStep []

/-- An unoccupied preference is taken without displacement. -/
theorem parkStep_of_not_mem (occupied : List Nat) (p : Nat) (h : p ∉ occupied) :
    parkStep occupied p = p := by
  rw [parkStep_eq, if_neg h]

/-- Parking never moves a car to the left of its preference. -/
theorem le_parkStep (occupied : List Nat) (p : Nat) : p ≤ parkStep occupied p := by
  induction occupied using (measure List.length).wf.induction generalizing p with
  | h occupied ih =>
    rw [parkStep_eq]
    split
    · rename_i hm
      have hl := List.length_erase_of_mem hm
      have hp := List.length_pos_of_mem hm
      have hh := ih (occupied.erase p)
        (by change (occupied.erase p).length < occupied.length; omega) (p + 1)
      omega
    · exact Nat.le_refl p

/-- The selected spot is vacant and every skipped spot was occupied. -/
theorem parkStep_spec (occupied : List Nat) (p : Nat) :
    parkStep occupied p ∉ occupied ∧
      ∀ q, p ≤ q → q < parkStep occupied p → q ∈ occupied := by
  induction occupied using (measure List.length).wf.induction generalizing p with
  | h occupied ih =>
    rw [parkStep_eq]
    split
    · rename_i h
      have he := List.length_erase_of_mem h
      have hp := List.length_pos_of_mem h
      have hh := ih (occupied.erase p)
        (by change (occupied.erase p).length < occupied.length; omega) (p + 1)
      have hl := le_parkStep (occupied.erase p) (p + 1)
      constructor
      · intro hm
        exact hh.1 ((List.mem_erase_of_ne (by omega)).mpr hm)
      · intro q hq hlt
        by_cases he : q = p
        · simpa [he] using h
        · exact List.mem_of_mem_erase (hh.2 q (by omega) hlt)
    · rename_i h
      exact ⟨h, by intros; omega⟩

/-- The local unit-displacement criterion depends only on two adjacent spots. -/
theorem parkStep_le_add_one_iff (occupied : List Nat) (p : Nat) :
    parkStep occupied p ≤ p + 1 ↔ p ∉ occupied ∨ p + 1 ∉ occupied := by
  constructor
  · intro h
    have hl := le_parkStep occupied p
    have hn := (parkStep_spec occupied p).1
    by_cases he : parkStep occupied p = p
    · exact Or.inl (he ▸ hn)
    · have he : parkStep occupied p = p + 1 := by omega
      exact Or.inr (he ▸ hn)
  · intro h
    rcases h with h | h
    · rw [parkStep_of_not_mem occupied p h]; omega
    · by_contra hn
      exact h ((parkStep_spec occupied p).2 (p + 1) (by omega) (by omega))

private theorem parkFrom_length (occupied a : List Nat) :
    (parkFrom occupied a).length = a.length := by
  induction a generalizing occupied with
  | nil => rfl
  | cons p a ih => simp only [parkFrom, List.length_cons, ih]

/-- There is one output spot per input car. -/
theorem spots_length (a : List Nat) : (spots a).length = a.length :=
  parkFrom_length [] a

private theorem rotateBlocks_perm (cut : Nat → Bool) (pending a : List Nat) :
    (rotateBlocks cut pending a).Perm (pending ++ a) := by
  induction a generalizing pending with
  | nil => simp [rotateBlocks]
  | cons y ys ih =>
    simp only [rotateBlocks]
    split
    · exact ((ih []).append_left (y :: pending)).trans (by
        simpa using (List.perm_middle.symm : (y :: (pending ++ ys)).Perm (pending ++ y :: ys)))
    · simpa only [List.append_assoc, List.singleton_append] using ih (pending ++ [y])

private theorem foataStep_perm (w : List Nat) (x : Nat) :
    (foataStep w x).Perm (w ++ [x]) := by
  exact (rotateBlocks_perm _ [] w).append_right [x]

private theorem foldl_foata_perm (a w : List Nat) :
    (a.foldl foataStep w).Perm (w ++ a) := by
  induction a generalizing w with
  | nil => simp
  | cons x a ih =>
    exact (ih (foataStep w x)).trans (by
      simpa only [List.append_assoc, List.singleton_append] using
        (foataStep_perm w x).append_right a)

/-- Foata's transformation preserves the multiset of letters. -/
theorem foata_perm (a : List Nat) : (foata a).Perm a :=
  foldl_foata_perm a []

/-- The implementation obeys the recursive last-letter equation. -/
theorem foata_append_singleton (a : List Nat) (x : Nat) :
    foata (a ++ [x]) = foataStep (foata a) x := by
  simp [foata, List.foldl_append]

private theorem parkFrom_eq_of_nodup (occupied a : List Nat) (ha : a.Nodup)
    (hd : ∀ x ∈ a, x ∉ occupied) : parkFrom occupied a = a := by
  induction a generalizing occupied with
  | nil => rfl
  | cons x a ih =>
    have hx := hd x (by simp)
    rw [parkFrom, parkStep_of_not_mem occupied x hx]
    congr 1
    apply ih (x :: occupied) ha.tail
    intro y hy hm
    rcases List.mem_cons.mp hm with he | hm
    · exact (List.nodup_cons.mp ha).1 (he ▸ hy)
    · exact hd y (by simp [hy]) hm

/-- Distinct preferences produce no displacement, on the total street. -/
theorem spots_eq_of_nodup (a : List Nat) (ha : a.Nodup) : spots a = a :=
  parkFrom_eq_of_nodup [] a ha (by simp)

/-- Unbounded fragment: commutation for all words with distinct letters.
This is not the unrestricted unit-interval conjecture. -/
theorem spot_foata_comm (a : List Nat) (ha : a.Nodup) :
    spots (foata a) = foata (spots a) := by
  rw [spots_eq_of_nodup a ha, spots_eq_of_nodup (foata a) ((foata_perm a).nodup_iff.mpr ha)]

/-- Increasing preferences and enlarging the occupied set cannot lower the chosen spot. -/
theorem parkStep_mono (occupied occupied' : List Nat) (p r : Nat)
    (hs : occupied ⊆ occupied') (hp : p ≤ r) :
    parkStep occupied p ≤ parkStep occupied' r := by
  by_contra h
  have hl := le_parkStep occupied' r
  have hm := (parkStep_spec occupied p).2 (parkStep occupied' r) (by omega) (by omega)
  exact (parkStep_spec occupied' r).1 (hs hm)

private theorem parkFrom_lower (occupied a : List Nat) (b : Nat)
    (hb : ∀ p ∈ a, b ≤ parkStep occupied p) :
    ∀ q ∈ parkFrom occupied a, b ≤ q := by
  induction a generalizing occupied with
  | nil => simp [parkFrom]
  | cons p a ih =>
    intro q hq
    simp only [parkFrom, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hb p (by simp)
    · apply ih (parkStep occupied p :: occupied) _ q hq
      intro r hr
      exact le_trans (hb r (by simp [hr]))
        (parkStep_mono occupied (parkStep occupied p :: occupied) r r
          (by intro x hx; simp [hx]) (le_refl r))

private theorem parkFrom_pairwise (occupied a : List Nat)
    (ha : a.Pairwise (· ≤ ·)) : (parkFrom occupied a).Pairwise (· ≤ ·) := by
  induction a generalizing occupied with
  | nil => simp [parkFrom]
  | cons p a ih =>
    rw [List.pairwise_cons] at ha
    simp only [parkFrom, List.pairwise_cons]
    refine ⟨?_, ih _ ha.2⟩
    apply parkFrom_lower
    intro r hr
    exact parkStep_mono occupied (parkStep occupied p :: occupied) p r
      (by intro x hx; simp [hx]) (ha.1 r hr)

/-- Parking a nondecreasing preference word gives a nondecreasing spot word. -/
theorem spots_pairwise (a : List Nat) (ha : a.Pairwise (· ≤ ·)) :
    (spots a).Pairwise (· ≤ ·) := parkFrom_pairwise [] a ha

private theorem rotateBlocks_of_all (cut : Nat → Bool) (a : List Nat)
    (ha : ∀ x ∈ a, cut x = true) : rotateBlocks cut [] a = a := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    simp only [rotateBlocks, ha x (by simp), ↓reduceIte,
      List.cons_append, List.nil_append]
    rw [ih (by intro y hy; exact ha y (by simp [hy]))]

private theorem foataStep_of_upper (a : List Nat) (x : Nat)
    (ha : ∀ y ∈ a, y ≤ x) : foataStep a x = a ++ [x] := by
  have hl : a.getLastD x ≤ x := by
    cases a with
    | nil => simp
    | cons y a =>
      apply ha
      simpa only [List.getLastD_cons] using
        (List.getLastD_mem_cons : a.getLastD y ∈ y :: a)
  simp only [foataStep, hl, ↓reduceIte]
  rw [rotateBlocks_of_all _ a (by intro y hy; simpa using ha y hy)]

/-- Foata fixes every nondecreasing word. -/
theorem foata_eq_of_pairwise (a : List Nat) (ha : a.Pairwise (· ≤ ·)) :
    foata a = a := by
  induction a using List.reverseRecOn with
  | nil => rfl
  | append_singleton a x ih =>
    rw [List.pairwise_append] at ha
    rw [foata_append_singleton, ih ha.1]
    apply foataStep_of_upper
    intro y hy
    exact ha.2.2 y hy x (by simp)

/-- A second unbounded fragment, allowing repeated letters in nondecreasing words. -/
theorem spot_foata_comm_of_pairwise (a : List Nat) (ha : a.Pairwise (· ≤ ·)) :
    spots (foata a) = foata (spots a) := by
  rw [foata_eq_of_pairwise a ha, foata_eq_of_pairwise (spots a) (spots_pairwise a ha)]

/-- Recursive unit-interval condition along the parking run. -/
def unitRun (n : Nat) (occupied : List Nat) : List Nat → Bool
  | [] => true
  | p :: a =>
      let q := parkStep occupied p
      decide (1 ≤ p ∧ p ≤ n ∧ q ≤ n ∧ q ≤ p + 1) && unitRun n (q :: occupied) a

private theorem unitRun_spec (n : Nat) (occupied a : List Nat) :
    unitRun n occupied a = true ↔
      (∀ p ∈ a, 1 ≤ p ∧ p ≤ n) ∧
      (∀ q ∈ parkFrom occupied a, 1 ≤ q ∧ q ≤ n) ∧
      (a.zip (parkFrom occupied a)).all (fun pq => pq.2 ≤ pq.1 + 1) = true := by
  induction a generalizing occupied with
  | nil => simp [unitRun, parkFrom]
  | cons p a ih =>
    have hl := le_parkStep occupied p
    simp only [unitRun, Bool.and_eq_true, decide_eq_true_eq, ih, parkFrom,
      List.forall_mem_cons, List.zip_cons_cons, List.all_cons]
    constructor
    · rintro ⟨⟨hp, hpn, hqn, hq⟩, ha, hs, hd⟩
      exact ⟨⟨⟨hp, hpn⟩, ha⟩, ⟨⟨by omega, hqn⟩, hs⟩, hq, hd⟩
    · rintro ⟨⟨⟨hp, hpn⟩, ha⟩, ⟨⟨_, hqn⟩, hs⟩, hq, hd⟩
      exact ⟨⟨hp, hpn, hqn, hq⟩, ha, hs, hd⟩

/-- The recursive unit-interval condition is equivalent to the parking and displacement definition. -/
theorem isUnitInterval_iff_unitRun (a : List Nat) :
    IsUnitInterval a ↔ unitRun a.length [] a = true := by
  rw [unitRun_spec]
  simp only [IsUnitInterval, IsParkingFunction, spots, and_assoc]

#print axioms parkStep
#print axioms parkFrom
#print axioms spots
#print axioms IsParkingFunction
#print axioms IsUnitInterval
#print axioms rotateBlocks
#print axioms foataStep
#print axioms foata
#print axioms parkStep_of_not_mem
#print axioms le_parkStep
#print axioms parkStep_spec
#print axioms parkStep_le_add_one_iff
#print axioms spots_length
#print axioms foata_perm
#print axioms foata_append_singleton
#print axioms spots_eq_of_nodup
#print axioms spot_foata_comm
#print axioms parkStep_mono
#print axioms spots_pairwise
#print axioms foata_eq_of_pairwise
#print axioms spot_foata_comm_of_pairwise
#print axioms unitRun
#print axioms isUnitInterval_iff_unitRun

end D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata
