/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The complete guarded five-hole source fiber and its two exact literal strata. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery (CutSet orderedHoles reachedHoles)
open ActualCutPartitionDecoder (HoleExterior cutExterior actualPartition literalRecord)
open NativeDepthPatterns (original_present_transport)

def F (y : Source) : Source := .mul (.of true) (substitution y)
def V (x y z : Source) : Source := .mul x (.mul y (.mul z (.mul (F y) (F z))))

def position : Fin 5 → Address :=
  ![[false], [true,false], [true,true,false],
    [true,true,true,false], [true,true,true,true]]

def Q : CutSet := {position 0, position 1, position 2, position 3, position 4}

def GuardedEqual (a : Nat) (p : Address) (b : Nat) (q : Address) (u : Source) : Prop :=
  (subtree p (substitution^[a] u)).isSome ∧
  (subtree q (substitution^[b] u)).isSome ∧
  subtree p (substitution^[a] u) = subtree q (substitution^[b] u)

/-- The complete one-hole root row has no restriction on its finite filling. -/
def rootLabel : HoleExterior × Finset (Address × Address) :=
  (.of (.inr []), {([],[])})

/-- All literal replies and both guards of each positive copy are retained. -/
def Raw (u : Source) : Prop :=
  literalRecord {[]} u = rootLabel ∧
  readout [] u = .branch ∧ readout [true] u = .branch ∧
  readout [true,true] u = .branch ∧ readout [true,true,true] u = .branch ∧
  readout [true,true,true,false,false] u = .alpha ∧
  readout [true,true,true,true,false] u = .alpha ∧
  GuardedEqual 0 [true,true,true,false,true] 1 (position 1) u ∧
  GuardedEqual 0 [true,true,true,true,true] 1 (position 2) u

theorem root_record (u : Source) : literalRecord {[]} u = rootLabel := by
  cases u <;>
    simp [literalRecord, cutExterior, actualPartition, orderedHoles, reachedHoles,
      rootLabel, subtree]

private theorem left_alpha (t : Source) (h : readout [false] t = .alpha) :
    ∃ r : Source, t = .mul (.of true) r := by
  cases t with
  | of b => simp [readout] at h
  | mul l r =>
      cases l with
      | of b => cases b <;> simp_all [readout]
      | mul a b => simp [readout] at h

/-- The converse extracts the first three whole holes from every raw source. -/
theorem raw_fiber_iff (u : Source) : Raw u ↔ ∃ x y z : Source, u = V x y z := by
  constructor
  · rintro ⟨_,root,r,rr,rrr,al,bl,copyA,copyB⟩
    cases u with
    | of b => cases b <;> simp [readout] at root
    | mul x s =>
      cases s with
      | of b => cases b <;> simp [readout] at r
      | mul y s =>
        cases s with
        | of b => cases b <;> simp [readout] at rr
        | mul z s =>
          cases s with
          | of b => cases b <;> simp [readout] at rrr
          | mul a b =>
            obtain ⟨ar,rfl⟩ := left_alpha a al
            obtain ⟨br,rfl⟩ := left_alpha b bl
            have ae : ar = substitution y := by
              simpa [GuardedEqual, subtree, position, map_mul] using copyA.2.2
            have be : br = substitution z := by
              simpa [GuardedEqual, subtree, position, map_mul] using copyB.2.2
            exact ⟨x,y,z,by simp [V,F,ae,be]⟩
  · rintro ⟨x,y,z,rfl⟩
    refine ⟨root_record _, ?_⟩
    simp [V, F, readout, GuardedEqual, subtree, position, map_mul]

/-- Original records contain the supplied addresses, not position numbers. -/
abbrev NegativeRecord := Nat × Address × Nat × Address
abbrev OriginalHistory := List NegativeRecord

def Supported (H : OriginalHistory) : Prop :=
  ∀ e ∈ H, e.2.1 ∈ Q ∧ e.2.2.2 ∈ Q

/-- Every finite original list between Q endpoints is retained verbatim. -/
abbrev History := {H : OriginalHistory // Supported H}

abbrev IndexedRecord := Nat × Fin 5 × Nat × Fin 5

def addressIndex (a : Address) : Fin 5 :=
  if a = position 0 then 0 else if a = position 1 then 1
  else if a = position 2 then 2 else if a = position 3 then 3 else 4

private theorem position_index (a : Address) (ha : a ∈ Q) :
    position (addressIndex a) = a := by
  simp only [Q,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide

def originalRecord (e : IndexedRecord) : NegativeRecord :=
  (e.1,position e.2.1,e.2.2.1,position e.2.2.2)

/-- The finite translation carries a proof of complete list reconstruction.
Epochs, order and duplicate occurrences are unchanged by both maps. -/
def indexedHistory (H : History) :
    {K : List IndexedRecord // K.map originalRecord = H.val} := by
  refine ⟨H.val.map (fun e =>
    (e.1,addressIndex e.2.1,e.2.2.1,addressIndex e.2.2.2)),?_⟩
  rw [List.map_map]
  conv_rhs => rw [← List.map_id H.val]
  apply List.map_congr_left
  intro e he
  obtain ⟨hp,hq⟩ := H.property e he
  simp only [Function.comp_apply,originalRecord,position_index _ hp,position_index _ hq]
  rcases e with ⟨a,p,b,q⟩
  rfl

/-- Both guards and the comparison concern entire transformed subtrees. -/
def Negative (e : NegativeRecord) (u : Source) : Prop :=
  (subtree e.2.1 (substitution^[e.1] u)).isSome ∧
  (subtree e.2.2.2 (substitution^[e.2.2.1] u)).isSome ∧
  subtree e.2.1 (substitution^[e.1] u) ≠
    subtree e.2.2.2 (substitution^[e.2.2.1] u)

def Protected (H : History) (u : Source) : Prop := ∀ e ∈ H.val, Negative e u
def D (H : History) (u : Source) : Prop := Raw u ∧ Protected H u

def hole (x y z : Source) : Fin 5 → Source := ![x,y,z,F y,F z]

private theorem hole_at (x y z : Source) (i : Fin 5) :
    subtree (position i) (V x y z) = some (hole x y z i) := by
  fin_cases i <;> rfl

/-- Every Q endpoint remains reached at every supplied natural epoch. -/
theorem epoch_hole (a : Nat) (x y z : Source) (i : Fin 5) :
    subtree (position i) (substitution^[a] (V x y z)) =
      some (substitution^[a] (hole x y z i)) :=
  original_present_transport a (position i) _ _ (hole_at x y z i)

def exterior : HoleExterior := .mul (.of (.inr (position 0)))
  (.mul (.of (.inr (position 1))) (.mul (.of (.inr (position 2)))
    (.mul (.of (.inr (position 3))) (.of (.inr (position 4))))))

def labelClass (side : Bool) (a : Address) : Nat :=
  if a = position 0 then 0 else if a = position 1 then (if side then 1 else 0)
  else if a = position 2 then (if side then 2 else 1)
  else if a = position 3 then (if side then 0 else 2) else 3

/-- The entire exterior and every ordered pair in the prescribed partition. -/
def label (side : Bool) : HoleExterior × Finset (Address × Address) :=
  (exterior, (Q.product Q).filter (fun pq => labelClass side pq.1 = labelClass side pq.2))

def Distinct (y z : Source) : Prop :=
  y ≠ z ∧ y ≠ F y ∧ y ≠ F z ∧ z ≠ F y ∧ z ≠ F z ∧ F y ≠ F z

def source (side : Bool) (y z : Source) : Source := V (if side then F y else y) y z

def Stratum (side : Bool) (H : History) (u : Source) : Prop :=
  D H u ∧ literalRecord Q u = label side

@[simp] private theorem exterior_stop (a : Address) (t : Source) (ha : a ∈ Q) :
    cutExterior Q a t = .of (.inr a) := by
  cases t <;> simp [cutExterior,ha]

@[simp] private theorem reached_stop (a : Address) (t : Source) (ha : a ∈ Q) :
    reachedHoles Q a t = [a] := by
  cases t <;> simp [reachedHoles,ha]

private theorem whole_exterior (x y z : Source) : cutExterior Q [] (V x y z) = exterior := by
  have h0 : ([] : Address) ∉ Q := by decide
  have h1 : ([true] : Address) ∉ Q := by decide
  have h2 : ([true,true] : Address) ∉ Q := by decide
  have h3 : ([true,true,true] : Address) ∉ Q := by decide
  simp only [V,cutExterior,List.nil_append,List.cons_append,
    h0,h1,h2,h3,if_false]
  rw [exterior_stop _ _ (by decide), exterior_stop _ _ (by decide),
    exterior_stop _ _ (by decide), exterior_stop _ _ (by decide),
    exterior_stop _ _ (by decide)]
  rfl

private theorem whole_holes (x y z : Source) :
    (orderedHoles Q (V x y z)).toFinset = Q := by
  have h0 : ([] : Address) ∉ Q := by decide
  have h1 : ([true] : Address) ∉ Q := by decide
  have h2 : ([true,true] : Address) ∉ Q := by decide
  have h3 : ([true,true,true] : Address) ∉ Q := by decide
  unfold orderedHoles
  simp only [V,reachedHoles,List.nil_append,List.cons_append,
    h0,h1,h2,h3,if_false]
  rw [reached_stop _ _ (by decide), reached_stop _ _ (by decide),
    reached_stop _ _ (by decide), reached_stop _ _ (by decide),
    reached_stop _ _ (by decide)]
  simp [Q,position]

private theorem partition_pair (x y z : Source) (i j : Fin 5) :
    (position i,position j) ∈ actualPartition Q (V x y z) ↔
      hole x y z i = hole x y z j := by
  have mem (k : Fin 5) : position k ∈ Q := by fin_cases k <;> simp [Q]
  simp [actualPartition, whole_holes,
    hole_at, mem]

/-- This is a full-label test, rather than a comparison of selected replies. -/
theorem complete_label_iff (side : Bool) (x y z : Source) :
    literalRecord Q (V x y z) = label side ↔
      x = (if side then F y else y) ∧ Distinct y z := by
  have membership (i j : Fin 5) :
      (position i,position j) ∈ (label side).2 ↔
        labelClass side (position i) = labelClass side (position j) := by
    have mem (k : Fin 5) : position k ∈ Q := by fin_cases k <;> simp [Q]
    simp [label,mem]
  constructor
  · intro eq
    have pairs (i j : Fin 5) :
        hole x y z i = hole x y z j ↔
          labelClass side (position i) = labelClass side (position j) := by
      rw [← partition_pair, ← membership]
      exact Finset.ext_iff.mp (congrArg Prod.snd eq) _
    have d : Distinct y z := by
      have p := pairs 1 2; have q := pairs 1 3; have r := pairs 1 4
      have s := pairs 2 3; have t := pairs 2 4; have v := pairs 3 4
      cases side <;> simp_all [Distinct,hole,labelClass,position]
    refine ⟨?_,d⟩
    cases side
    · simpa [hole,labelClass,position] using (pairs 0 1).mpr (by decide)
    · simpa [hole,labelClass,position] using (pairs 0 3).mpr (by decide)
  · rintro ⟨rfl,d⟩
    obtain ⟨dyz,dyfy,dyfz,dzfy,dzfz,dfyfz⟩ := d
    have tests (i j : Fin 5) :
        hole (if side then F y else y) y z i =
          hole (if side then F y else y) y z j ↔
        labelClass side (position i) = labelClass side (position j) := by
      fin_cases i <;> fin_cases j <;> cases side
      all_goals first
        | exact iff_of_true rfl rfl
        | exact iff_of_false dyz (by decide)
        | exact iff_of_false dyfy (by decide)
        | exact iff_of_false dyfz (by decide)
        | exact iff_of_false dzfy (by decide)
        | exact iff_of_false dzfz (by decide)
        | exact iff_of_false dfyfz (by decide)
        | exact iff_of_false (Ne.symm dyz) (by decide)
        | exact iff_of_false (Ne.symm dyfy) (by decide)
        | exact iff_of_false (Ne.symm dyfz) (by decide)
        | exact iff_of_false (Ne.symm dzfy) (by decide)
        | exact iff_of_false (Ne.symm dzfz) (by decide)
        | exact iff_of_false (Ne.symm dfyfz) (by decide)
    apply Prod.ext (whole_exterior _ _ _)
    change actualPartition Q _ = (label side).2
    apply Finset.ext
    rintro ⟨a,b⟩
    simp only [actualPartition, whole_holes,
      label, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
    by_cases ha : a ∈ Q
    · by_cases hb : b ∈ Q
      · simp only [ha,hb,true_and]
        rw [← position_index a ha, ← position_index b hb, hole_at, hole_at,
          Option.some.injEq]
        exact tests (addressIndex a) (addressIndex b)
      · simp [hb]
    · simp [ha]

/-- Raw-source membership in either complete stratum has an exact converse. -/
theorem raw_stratum_iff (side : Bool) (H : History) (u : Source) :
    Stratum side H u ↔ ∃ y z : Source,
      u = source side y z ∧ Distinct y z ∧ Protected H (source side y z) := by
  constructor
  · rintro ⟨⟨raw,hist⟩,row⟩
    obtain ⟨x,y,z,rfl⟩ := (raw_fiber_iff u).mp raw
    obtain ⟨rfl,distinct⟩ := (complete_label_iff side x y z).mp row
    exact ⟨y,z,rfl,distinct,hist⟩
  · rintro ⟨y,z,rfl,distinct,hist⟩
    refine ⟨⟨(raw_fiber_iff _).mpr ⟨_,y,z,rfl⟩,hist⟩,?_⟩
    exact (complete_label_iff side _ y z).mpr ⟨rfl,distinct⟩

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
