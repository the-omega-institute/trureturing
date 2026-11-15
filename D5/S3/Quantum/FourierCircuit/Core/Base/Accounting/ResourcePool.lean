/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Accounting/ResourcePool
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Licensed original QFT circuit proof support. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0; the full license is in
Library/Quantum/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Core/Base/Accounting/ResourcePool.lean.
Authors: QudeLeap Team
-/

module

import Mathlib.Init
public import D5.S3.Quantum.FourierCircuit.Core.Base.Accounting.Event
import all D5.S3.Quantum.FourierCircuit.Core.Base.Accounting.Event
public import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.OrderedMonoid
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Multiset.UnionInter

/-!
# Strict event resource pools

`ResourcePool model` is a finite multiset over execution-event coordinates.
Run-derived pools record occurrences, while problem-owned pools state bounds
over the same coordinates.  Equality, addition, repetition, and order are
literal coordinate operations on identical event labels.  This module contains
no live-capacity axis and performs no compilation, expansion, pooling, or model
conversion; the type alone is not execution-provenance evidence.
-/

section

namespace QuantumAlg

/-- A finite event ledger whose coordinates are fixed by the selected execution model. -/
public abbrev ResourcePool (model : ExecutionModel) := Multiset (Resource.Event model)

namespace ResourcePool

/-- A pool containing `multiplicity` copies of one event coordinate. -/
@[expose]
public def singleton {model : ExecutionModel} (event : Resource.Event model)
    (multiplicity : Nat := 1) : ResourcePool model :=
  Multiset.replicate multiplicity event

/-- The exact multiplicity of one event coordinate. -/
public def count {model : ExecutionModel} (event : Resource.Event model)
    (pool : ResourcePool model) : Nat :=
  Multiset.count event pool
ool model) : ResourcePool model :=
  multiplicity • pool

/-- Convert an actual event list into its literal multiplicity ledger. -/
@[expose]
public def ofList {model : ExecutionModel}
    (events : List (Resource.Event model)) : ResourcePool model :=
  events
try.2 + ofCounts entries
t : ResourcePool model) : ResourcePool model :=
  left ∪ right
source.Event.liftClassical

@[simp] lemma count_zero {model : ExecutionModel} (event : Resource.Event model) :
    count event (0 : ResourcePool model) = 0 := by
  simp [count]
del : ExecutionModel} (event : Resource.Event model) :
    singleton event 0 = 0 := rfl

/-- Count one native coordinate in an arbitrary singleton ledger. -/
@[simp] lemma count_singleton {model : ExecutionModel}
    (target event : Resource.Event model) (multiplicity : Nat) :
    count target (singleton event multiplicity) =
      if event = target then multiplicity else 0 := by
  simp [count, singleton, Multiset.count_replicate]
unt event (singleton event multiplicity) = multiplicity := by
  simp
ngleton, Multiset.count_replicate, if_neg (Ne.symm hne)]

@[simp] lemma count_add {model : ExecutionModel} (event : Resource.Event model)
    (left right : ResourcePool model) :
    count event (left + right) = count event left + count event right := by
  simp [count]
rt, fresh, induction]
  simpa using aux Finset.univ
e multiplicity pool) = multiplicity * count event pool := by
  simp [count, scale]
vent pool := by
  simpa only [scale] using count_scale event multiplicity pool

@[simp] public lemma count_ofList {model : ExecutionModel} (event : Resource.Event model)
    (events : List (Resource.Event model)) :
    count event (ofList events) = List.count event events := by
  change Multiset.count event (Multiset.ofList events) = List.count event events
  exact Multiset.coe_count event events
fList ([] : List (Resource.Event model)) = 0 :=
  rfl

@[simp] lemma ofList_cons {model : ExecutionModel} (event : Resource.Event model)
    (events : List (Resource.Event model)) :
    ofList (event :: events) = singleton event + ofList events := by
  simp [ofList, singleton]

@[simp] lemma ofList_append {model : ExecutionModel}
    (first second : List (Resource.Event model)) :
    ofList (first ++ second) = ofList first + ofList second := by
  simp [ofList]
ts ([] : List (Resource.Event model × Nat)) = 0 := rfl
 entry.2 + ofCounts entries := rfl
unt event (ofCounts ([] : List (Resource.Event model × Nat))) = 0 := by
  simp
  count target (ofCounts entries) := by
  simp
Counts ((event, 0) :: entries) = ofCounts entries := by
  simp
ent + ofCounts entries
  rw [← add_assoc, ← Multiset.replicate_add]
      exact ihFirst.trans ihSecond
x left right) = Nat.max (count event left) (count event right) := by
  simp [count, max]
ol = 0 := by
  simp [scale]
smul, add_comm]
cons, countIH, scale_succ]

  simpa [count] using (Multiset.le_iff_count (s := left) (t := right))
₁ + right₂ :=
  add_le_add first second
o event
  simp
o event
  simp
t.mp rightBound) event⟩
 bound) event)
model.classicalOracles)) = 0 := rfl
ft + liftClassical right := by
  simp [liftClassical]
l (model := model)) multiplicity pool
iftClassical event) multiplicity := by
  simp [liftClassical, singleton]
).eq_iff] using
    (Multiset.count_eq_card_filter_eq pool event).symm
ap_injective (Resource.Event.liftClassical_injective model)
= by
  exact Multiset.map_le_map_iff (Resource.Event.liftClassical_injective model)
hip
  cases event <;> first | (cases ‹Empty›) | (cases equality)
hip
  cases event <;> first | (cases ‹Empty›) | (cases equality)
hip
  cases event <;> first | (cases ‹Empty›) | (cases equality)
hip
  cases event <;> first | (cases ‹Empty›) | (cases equality)
y] at coefficientBound
  exact (Nat.not_le_of_lt positive) coefficientBound

end ResourcePool
end QuantumAlg

end
