/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativePayloadHistoryInstallation
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite actual history records install arbitrary native mixed payloads exactly. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
import D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout acquisitionTrace)
open ActualLeafHistoryRigidity (subtree)
open NativePrefixIdentityReflection (MixedExpr eval)
open NativeFiveHoleFiber (GuardedEqual)

/-- Literal and positive records retain the actual epoch and original address. -/
inductive Record where
  | literal : Nat → Address → Reply → Record
  | positive : Nat → Address → Nat → Address → Record

/-- Both endpoints of a positive record must be reached in the same source. -/
def Record.Holds (U : Source) : Record → Prop
  | .literal a p y => readout p (substitution^[a] U) = y
  | .positive a p b q => GuardedEqual a p b q U

def Holds (U : Source) (H : List Record) : Prop := ∀ r ∈ H, r.Holds U

/-- Only occurring generator names require an original-location premise. -/
def names {ι : Type} : MixedExpr ι → List ι
  | .ground _ => []
  | .residual _ i => [i]
  | .pair E F => names E ++ names F

/-- Every constructor and terminal leaf of a ground is retained. -/
def groundRecords (p : Address) (g : Source) : List Record :=
  (acquisitionTrace p g).map (fun r => .literal 0 r.1 r.2)

/-- Compilation depends only on the finite syntax and original locators. -/
def compile {ι : Type} (loc : ι → Address) (p : Address) : MixedExpr ι → List Record
  | .ground g => groundRecords p g
  | .residual a i => [.positive 0 p a (loc i)]
  | .pair E F => .literal 0 p .branch ::
      (compile loc (p ++ [false]) E ++ compile loc (p ++ [true]) F)

private theorem readout_at (p : Address) (U : Source) :
    readout p U = match subtree p U with
      | none => .absent
      | some T => readout [] T := by
  have h := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p [] U
  cases hs : subtree p U <;> simpa only [List.append_nil, hs] using h

private theorem leaf_exact (p : Address) (U : Source) (b : Bool) :
    readout p U = (if b then .alpha else .beta) ↔ subtree p U = some (.of b) := by
  rw [readout_at]
  cases h : subtree p U with
  | none => cases b <;> simp
  | some T =>
      cases T with
      | of c =>
          cases b <;> cases c <;> simp [readout]
          all_goals intro h; cases h
      | mul l r => cases b <;> simp [readout]

private theorem pair_exact (p : Address) (U l r : Source) :
    readout p U = .branch ∧
      subtree (p ++ [false]) U = some l ∧ subtree (p ++ [true]) U = some r ↔
    subtree p U = some (.mul l r) := by
  have append :=
    ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [readout_at, append p [false] U, append p [true] U]
  cases h : subtree p U with
  | none => simp
  | some T =>
      cases T with
      | of b => cases b <;> simp [readout, subtree]
      | mul a b =>
          simp only [readout, subtree, Option.bind_some, Option.some.injEq, true_and]
          constructor
          · rintro ⟨rfl,rfl⟩; rfl
          · intro h; injection h with ha hb; exact ⟨ha,hb⟩

private theorem trace_exact (p : Address) (g U : Source) :
    (∀ r ∈ acquisitionTrace p g, readout r.1 U = r.2) ↔ subtree p U = some g := by
  induction g generalizing p with
  | of b =>
      simpa only [acquisitionTrace, List.forall_mem_singleton] using leaf_exact p U b
  | mul l r ihl ihr =>
      simp only [acquisitionTrace, List.forall_mem_cons, List.forall_mem_append, ihl, ihr]
      exact pair_exact p U l r

/-- The generated actual records hold exactly when the payload root has its
interpreted value. Locator and payload addresses may overlap; this equivalence
makes no assertion that a compatible source exists for every valuation. -/
theorem payload_history_exact {ι : Type} (E : MixedExpr ι) (loc : ι → Address)
    (p : Address) (U : Source) (z : ι → Source)
    (located : ∀ i ∈ names E, subtree (loc i) U = some (z i)) :
    Holds U (compile loc p E) ↔ subtree p U = some (eval z E) := by
  induction E generalizing p with
  | ground g =>
      simpa only [compile, groundRecords, Holds, List.forall_mem_map,
        Record.Holds, Function.iterate_zero, id_eq, eval] using trace_exact p g U
  | residual a i =>
      have generator := NativeDepthPatterns.original_present_transport a (loc i) U (z i)
        (located i (by simp [names]))
      simp [compile, Holds, Record.Holds, GuardedEqual, generator, eval,
        Option.isSome_iff_exists]
      intro h; exact ⟨_,h⟩
  | pair E F ihE ihF =>
      have le : ∀ i ∈ names E, subtree (loc i) U = some (z i) :=
        fun i hi => located i (by simp [names, hi])
      have ri : ∀ i ∈ names F, subtree (loc i) U = some (z i) :=
        fun i hi => located i (by simp [names, hi])
      change Holds U (.literal 0 p .branch ::
        (compile loc (p ++ [false]) E ++ compile loc (p ++ [true]) F)) ↔ _
      simp only [Holds, List.forall_mem_cons, List.forall_mem_append]
      change readout p U = .branch ∧ Holds U (compile loc (p ++ [false]) E) ∧
        Holds U (compile loc (p ++ [true]) F) ↔ _
      rw [ihE _ le, ihF _ ri]
      exact pair_exact p U (eval z E) (eval z F)

end D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation
