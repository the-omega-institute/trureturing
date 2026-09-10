/- GID: D5/S3/ConceptDynamics/Spacetime/ComplementCharge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/ComplementCharge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Context-preserving event complement has the exact affine signed readout and the necessary balance guard. -/

import D5.S0.History.Spacetime.ArchiveCarrier
import D5.S3.ConceptDynamics.Negation.ComplementFiberLift
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.ComplementCharge

open D5.S0.History.Spacetime.ArchiveCarrier
open Negation.RelativeComplement Negation.ComplementFiberLift
noncomputable section

def contribution {d : Nat} (c : Context d) (e : c.Event) : Int :=
  if (c.archive.attributes e).positive then 1 else -1

theorem contribution_sign {d : Nat} (c : Context d) (e : c.Event) :
    contribution c e = 1 ∨ contribution c e = -1 := by
  unfold contribution
  split <;> simp

def charge {d : Nat} (c : Context d) (s : Finset c.Event) : Int :=
  ∑ e ∈ s, contribution c e

def readout {d : Nat} {c : Context d} (a : Selection c) : Int := charge c a.val

def background {d : Nat} (c : Context d) : Int := charge c c.current

def Balanced {d : Nat} (c : Context d) : Prop := background c = 0

def q {d : Nat} (x : Rich d) : Int := readout x.2

def BalancedRich (d : Nat) := {x : Rich d // Balanced x.1}

def emptySelection {d : Nat} (c : Context d) : Selection c := ⟨∅, Finset.empty_subset _⟩

def fullSelection {d : Nat} (c : Context d) : Selection c := ⟨c.current, Finset.Subset.refl _⟩

def complement {d : Nat} {c : Context d} (a : Selection c) : Selection c := by
  classical
  exact ⟨c.current \ a.val, Finset.sdiff_subset⟩

/-- Literal event complement, transported to the existing relative-complement API. -/
theorem complement_as_relative {d : Nat} {c : Context d} (a : Selection c) :
    ((complement a).val : Set c.Event) = relativeComplement c.current a.val := by
  classical
  exact Finset.coe_sdiff _ _

@[simp] theorem complement_involutive {d : Nat} {c : Context d} (a : Selection c) :
    complement (complement a) = a := by
  classical
  exact Subtype.ext (Finset.sdiff_sdiff_eq_self a.property)

theorem complement_readout {d : Nat} {c : Context d} (a : Selection c) :
    readout (complement a) = background c - readout a := by
  classical
  exact Finset.sum_sdiff_eq_sub a.property

@[simp] theorem empty_readout {d : Nat} (c : Context d) : readout (emptySelection c) = 0 := by
  simp [readout, emptySelection, charge]

/-- The balance condition concerns only the current region and is necessary as well as sufficient. -/
theorem balanced_iff_complement_negates {d : Nat} (c : Context d) :
    Balanced c ↔ ∀ a : Selection c, readout (complement a) = -readout a := by
  constructor
  · intro h a
    rw [complement_readout, h, zero_sub]
  · intro h
    have hz := h (emptySelection c)
    simpa [complement_readout, Balanced] using hz

def complementRich {d : Nat} (x : Rich d) : Rich d := ⟨x.1, complement x.2⟩

@[simp] theorem complementRich_involutive {d : Nat} (x : Rich d) :
    complementRich (complementRich x) = x := by
  cases x; simp [complementRich]; rfl

def complementBalanced {d : Nat} (x : BalancedRich d) : BalancedRich d :=
  ⟨complementRich x.val, x.property⟩

theorem complementBalanced_readout {d : Nat} (x : BalancedRich d) :
    q (complementBalanced x).val = -q x.val :=
  (balanced_iff_complement_negates x.val.1).mp x.property x.val.2

/-- A numerical opposite fiber is a set of selections, separate from event complement. -/
def oppositeFiber {d : Nat} {c : Context d} (a : Selection c) : Set (Selection c) :=
  complementFiber readout Neg.neg a

theorem balanced_complement_mem_oppositeFiber {d : Nat} {c : Context d} (h : Balanced c) :
    ∀ a : Selection c, complement a ∈ oppositeFiber a :=
  (isComplementLift_iff_mem_fiber readout Neg.neg complement).mp
    ((balanced_iff_complement_negates c).mp h)

/-- The finite sum equals the number of positive events minus the number of negative events. -/
theorem charge_eq_signed_card {d : Nat} (c : Context d) (s : Finset c.Event) :
    charge c s = (s.filter (fun e => (c.archive.attributes e).positive)).card -
      (s.filter (fun e => !(c.archive.attributes e).positive)).card := by
  classical
  simp [charge, contribution, Finset.sum_ite, sub_eq_add_neg]

end
end D5.S3.ConceptDynamics.Spacetime.ComplementCharge
