/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Six simultaneous actual repeated-partner sources and their exact all-address occurrence-cone restriction. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery
open NativeClassRootImage (OriginFiber)

/-- The original alpha orbit, with beta at index one. -/
def orbit : Nat → Source
  | 0 => .of true
  | n+1 => substitution (orbit n)

/-- Eight literal cut occurrences; false is left and true is right. -/
def position : Fin 8 → Address :=
  ![[false,false,false], [false,false,true], [false,true,false], [false,true,true],
    [true,false,false], [true,false,true], [true,true,false], [true,true,true]]

def P : CutSet := Finset.univ.image position

/-- Repeated coordinates are actual repeated finite subtree values. -/
def filling (x : Fin 6 → Source) : Source :=
  .mul (.mul (.mul (x 0) (x 1)) (.mul (x 0) (x 2)))
       (.mul (.mul (x 3) (x 4)) (.mul (x 3) (x 5)))

/-- Canonical first occurrence ordinals, rather than consecutive class labels. -/
def row : LiteralRow :=
  .mul (.mul (.mul (.of (.inr 0)) (.of (.inr 1)))
             (.mul (.of (.inr 0)) (.of (.inr 3))))
       (.mul (.mul (.of (.inr 4)) (.of (.inr 5)))
             (.mul (.of (.inr 4)) (.of (.inr 7))))

/-- Indices zero and one are the two zero targets; two through five are 1..4. -/
def label (z : Fin 6) : Fin 5 := ⟨if z.val < 2 then 0 else z.val - 1, by split_ifs <;> omega⟩

def groupA (z : Fin 6) : Bool := decide (z.val = 0 ∨ z.val = 2 ∨ z.val = 3)

def values (z : Fin 6) : Fin 6 → Source :=
  ![if groupA z then .of false else orbit 2,
    if z.val = 2 then .of true else orbit 4,
    if z.val = 3 then .of true else orbit 5,
    if groupA z then orbit 3 else .of false,
    if z.val = 4 then .of true else orbit 6,
    if z.val = 5 then .of true else orbit 7]

def current (z : Fin 6) : Source := filling (values z)

/-- The actual inverse at each depth-two pair: the exceptional pair becomes beta. -/
def origin (z : Fin 6) : Source :=
  let a := if groupA z then .of true else orbit 1
  let c := if groupA z then orbit 2 else .of true
  .mul (.mul (if z.val = 2 then .of false else .mul a (orbit 3))
              (if z.val = 3 then .of false else .mul a (orbit 4)))
       (.mul (if z.val = 4 then .of false else .mul c (orbit 5))
              (if z.val = 5 then .of false else .mul c (orbit 6)))

/-- The five complete canonical predecessor rows. A surviving repeated partner
is a hole, even when its other occurrence is replaced by concrete beta. -/
def predecessor : Fin 5 → LiteralRow :=
  ![row,
    .mul (.mul (.of (.inl false)) (.mul (.of (.inr 0)) (.of (.inr 1))))
         (.mul (.mul (.of (.inr 2)) (.of (.inr 3))) (.mul (.of (.inr 2)) (.of (.inr 5)))),
    .mul (.mul (.mul (.of (.inr 0)) (.of (.inr 1))) (.of (.inl false)))
         (.mul (.mul (.of (.inr 2)) (.of (.inr 3))) (.mul (.of (.inr 2)) (.of (.inr 5)))),
    .mul (.mul (.mul (.of (.inr 0)) (.of (.inr 1))) (.mul (.of (.inr 0)) (.of (.inr 3))))
         (.mul (.of (.inl false)) (.mul (.of (.inr 4)) (.of (.inr 5)))),
    .mul (.mul (.mul (.of (.inr 0)) (.of (.inr 1))) (.mul (.of (.inr 0)) (.of (.inr 3))))
         (.mul (.mul (.of (.inr 4)) (.of (.inr 5))) (.of (.inl false)))]

def holeList : Fin 5 → List Address :=
  ![[position 0,position 1,position 2,position 3,position 4,position 5,position 6,position 7],
    [position 2,position 3,position 4,position 5,position 6,position 7],
    [position 0,position 1,position 4,position 5,position 6,position 7],
    [position 0,position 1,position 2,position 3,position 6,position 7],
    [position 0,position 1,position 2,position 3,position 4,position 5]]

private theorem sorted_holes (t : Source) (l : List Address)
    (holes : reachedHoles P [] t = l) (distinct : l.Nodup)
    (ordered : l.Pairwise (fun a b => a ≤ b)) : orderedHoles P t = l := by
  rw [orderedHoles,holes]
  exact (List.toFinset_sort _ distinct).mpr ordered

theorem prefix_free : CutPrefixFree P := by
  intro a ha b hb h
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
  apply h.eq_of_length
  have hi : (position i).length = 3 := by fin_cases i <;> rfl
  have hj : (position j).length = 3 := by fin_cases j <;> rfl
  exact hi.trans hj.symm

private def names (t : Source) (l : List Address) (a : Address) : Nat :=
  firstEqIndex (subtree a t) (l.map (fun q => subtree q t))

private theorem named_row (t : Source) (l : List Address)
    (holes : orderedHoles P t = l) :
    canonicalRow P t = ActualCutPartitionDecoder.nameExterior (names t l)
      (ActualCutPartitionDecoder.cutExterior P [] t) := by
  apply Eq.symm
  apply ActualCutPartitionDecoder.nameExterior_correct P prefix_free
  · intro a _
    simp only [names,classOrdinal,holes]
  · rfl

set_option maxHeartbeats 1600000 in
/-- The actual six witnesses preserve the entire current partition and every
literal predecessor row, not just five output labels. -/
theorem six_source_realization :
    (∀ z : Fin 6, substitution (origin z) = current z ∧
      canonicalRow P (current z) = row ∧
      canonicalRow P (origin z) = predecessor (label z)) ∧
    Function.Injective predecessor := by
  have currentHoles : ∀ z : Fin 6, orderedHoles P (current z) = holeList 0 := by
    intro z
    apply sorted_holes
    · revert z; decide +kernel
    · decide +kernel
    · decide +kernel
  have originHoles : ∀ z : Fin 6, orderedHoles P (origin z) = holeList (label z) := by
    intro z
    apply sorted_holes
    · revert z; decide +kernel
    · revert z; decide +kernel
    · revert z; decide +kernel
  constructor
  · intro z
    have image : substitution (origin z) = current z := by revert z; decide +kernel
    refine ⟨image,?_,?_⟩
    · rw [named_row _ _ (currentHoles z)]
      revert z
      decide +kernel
    · rw [named_row _ _ (originHoles z)]
      revert z
      decide +kernel
  · decide +kernel

/-- The whole original infinite origin fiber. -/
abbrev Fiber := OriginFiber P row

def actual (z : Fin 6) : Fiber :=
  ⟨origin z, by rw [(six_source_realization.1 z).1]; exact (six_source_realization.1 z).2.1⟩

/-- The coordinate at a literal occurrence retains both occurrences of each partner. -/
def occurrenceClass : Fin 8 → Fin 6 := ![0,1,0,2,3,4,3,5]

/-- An arbitrary suffix is read in the exact same actual subtree. -/
theorem occurrence_read (p : Fin 8) (w : Address) (z : Fin 6) :
    readout (position p ++ w) (current z) = readout w (values z (occurrenceClass p)) := by
  fin_cases p <;> rfl

/-- Zero denotes a partner cone; positive locations denote their right cones.
The skeleton has no location. This function reads the literal address alone. -/
def location : Address → Option (Fin 5)
  | false :: false :: false :: _ => some 0
  | false :: false :: true :: _ => some 1
  | false :: true :: false :: _ => some 0
  | false :: true :: true :: _ => some 2
  | true :: false :: false :: _ => some 0
  | true :: false :: true :: _ => some 3
  | true :: true :: false :: _ => some 0
  | true :: true :: true :: _ => some 4
  | _ => none

/-- A proof-only factor of the native reply, not an additional query operation. -/
def question (a : Address) (z : Fin 6) : Bool :=
  match location a with
  | none => false
  | some j => if j = 0 then groupA z else decide (z.val = j.val + 1)

/-- Every finite address, including absent, deep and repeated reads, factors
through precisely its partner-group or positive-singleton split. -/
theorem all_address_factor (a : Address) :
    ∃ f : Bool → Reply, ∀ z : Fin 6, readout a (current z) = f (question a z) := by
  rcases a with _ | ⟨b,a⟩
  · exact ⟨fun _ => .branch, fun _ => rfl⟩
  rcases a with _ | ⟨c,a⟩
  · cases b <;> exact ⟨fun _ => .branch, fun _ => rfl⟩
  rcases a with _ | ⟨d,w⟩
  · cases b <;> cases c <;> exact ⟨fun _ => .branch, fun _ => rfl⟩
  cases b <;> cases c <;> cases d
  · refine ⟨fun t => readout w (if t then .of false else orbit 2), ?_⟩
    intro z
    change readout (position 0 ++ w) (current z) = _
    rw [occurrence_read]
    rfl
  · refine ⟨fun t => readout w (if t then .of true else orbit 4), ?_⟩
    intro z
    change readout (position 1 ++ w) (current z) = _
    rw [occurrence_read]
    change readout w (if z.val = 2 then .of true else orbit 4) =
      readout w (if decide (z.val = 2) then .of true else orbit 4)
    simp
  · refine ⟨fun t => readout w (if t then .of false else orbit 2), ?_⟩
    intro z
    change readout (position 2 ++ w) (current z) = _
    rw [occurrence_read]
    rfl
  · refine ⟨fun t => readout w (if t then .of true else orbit 5), ?_⟩
    intro z
    change readout (position 3 ++ w) (current z) = _
    rw [occurrence_read]
    change readout w (if z.val = 3 then .of true else orbit 5) =
      readout w (if decide (z.val = 3) then .of true else orbit 5)
    simp
  · refine ⟨fun t => readout w (if t then orbit 3 else .of false), ?_⟩
    intro z
    change readout (position 4 ++ w) (current z) = _
    rw [occurrence_read]
    rfl
  · refine ⟨fun t => readout w (if t then .of true else orbit 6), ?_⟩
    intro z
    change readout (position 5 ++ w) (current z) = _
    rw [occurrence_read]
    change readout w (if z.val = 4 then .of true else orbit 6) =
      readout w (if decide (z.val = 4) then .of true else orbit 6)
    simp
  · refine ⟨fun t => readout w (if t then orbit 3 else .of false), ?_⟩
    intro z
    change readout (position 6 ++ w) (current z) = _
    rw [occurrence_read]
    rfl
  · refine ⟨fun t => readout w (if t then .of true else orbit 7), ?_⟩
    intro z
    change readout (position 7 ++ w) (current z) = _
    rw [occurrence_read]
    change readout w (if z.val = 5 then .of true else orbit 7) =
      readout w (if decide (z.val = 5) then .of true else orbit 7)
    simp

#print axioms prefix_free
#print axioms six_source_realization
#print axioms occurrence_read
#print axioms all_address_factor
end D5.S3.Arith.FibonacciAtomic.Observer.NativeSixSourceCones
