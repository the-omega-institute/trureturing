/- GID: D5/S3/ConceptDynamics/Spacetime/ProductNodes
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/ProductNodes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Product events encode both archives and all current parent pairs. -/

import D5.S3.ConceptDynamics.Spacetime.ParallelComposition
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.ProductNodes

open D5.S0.History.Spacetime.HFEncoding
open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S0.History.Spacetime.SourceTreeEncoding
open ComplementCharge TaggedPresentation
noncomputable section

variable {d : Nat}

abbrev Parents (c e : Context d) := ↥c.current × ↥e.current
abbrev Node (c e : Context d) := (c.Event ⊕ e.Event) ⊕ Parents c e

def oldLeft (c e : Context d) (a : c.Event) : Node c e := .inl (.inl a)
def oldRight (c e : Context d) (b : e.Event) : Node c e := .inl (.inr b)
def generated (c e : Context d) (p : Parents c e) : Node c e := .inr p

def eventCode (c e : Context d) : Node c e → HF
  | .inl x => ParallelComposition.eventCode c.archive e.archive x
  | .inr p => eventTag 2 (pair p.1.val.val p.2.val.val)

theorem eventCode_injective (c e : Context d) : Function.Injective (eventCode c e) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (ParallelComposition.eventCode_injective _ _ h)
    | inr q => cases x <;> simp [eventCode, ParallelComposition.eventCode] at h
  | inr p =>
    cases y with
    | inl y => cases y <;> simp [eventCode, ParallelComposition.eventCode] at h
    | inr q =>
      have hh := pair_inj.mp (eventTag_inj.mp h).2
      exact congrArg Sum.inr (Prod.ext (Subtype.ext (Subtype.ext hh.1))
        (Subtype.ext (Subtype.ext hh.2)))

def code (c e : Context d) : Node c e ↪ HF := ⟨eventCode c e, eventCode_injective c e⟩

@[simp] theorem code_left (c e : Context d) (a : c.Event) :
    code c e (oldLeft c e a) = eventTag 0 a.val := rfl

@[simp] theorem code_right (c e : Context d) (b : e.Event) :
    code c e (oldRight c e b) = eventTag 1 b.val := rfl

@[simp] theorem code_generated (c e : Context d) (p : Parents c e) :
    code c e (generated c e p) = eventTag 2 (pair p.1.val.val p.2.val.val) := rfl

/-- Only the two actual parents determine the generated time and other attributes. -/
def generatedAttributes (c e : Context d) (p : Parents c e) : Attributes d where
  time := max (c.archive.attributes p.1.val).time (e.archive.attributes p.2.val).time + 1
  position i := (c.archive.attributes p.1.val).position i +
    (e.archive.attributes p.2.val).position i
  positive := (c.archive.attributes p.1.val).positive == (e.archive.attributes p.2.val).positive
  source := FreeMagma.mul (c.archive.attributes p.1.val).source
    (e.archive.attributes p.2.val).source

def attributes (c e : Context d) : Node c e → Attributes d
  | .inl x => ParallelComposition.attributes c.archive e.archive x
  | .inr p => generatedAttributes c e p

@[simp] theorem attributes_left (c e : Context d) (a : c.Event) :
    attributes c e (oldLeft c e a) = c.archive.attributes a := rfl

@[simp] theorem attributes_right (c e : Context d) (b : e.Event) :
    attributes c e (oldRight c e b) = e.archive.attributes b := rfl

@[simp] theorem attributes_generated (c e : Context d) (p : Parents c e) :
    attributes c e (generated c e p) = generatedAttributes c e p := rfl

theorem generated_contribution (c e : Context d) (p : Parents c e) :
    (if (generatedAttributes c e p).positive then (1 : Int) else -1) =
      contribution c p.1.val * contribution e p.2.val := by
  cases hc : (c.archive.attributes p.1.val).positive <;>
    cases he : (e.archive.attributes p.2.val).positive <;>
    simp [generatedAttributes, contribution, hc, he]

/-- Ordered tree pairing commutes with the literal source encoder; no leaf is renamed. -/
theorem source_code_generated (c e : Context d) (p : Parents c e) :
    sourceCode (generatedAttributes c e p).source =
      pair (natCode 1) (pair (sourceCode (c.archive.attributes p.1.val).source)
        (sourceCode (e.archive.attributes p.2.val).source)) := rfl

theorem hf_code_generated (c e : Context d) (p : Parents c e) :
    toZF (code c e (generated c e p)) = ZFSet.pair (Ordinal.toZFSet (2 : Ordinal))
      (ZFSet.pair (toZF p.1.val.val) (toZF p.2.val.val)) := by
  simp [eventTag]

/-- Selection containment provides the current-parent subtype, without changing its name. -/
def selectedParents {c : Context d} (a : Selection c) : Finset ↥c.current := by
  classical
  exact a.val.subtype (· ∈ c.current)

@[simp] theorem mem_selectedParents {c : Context d} (a : Selection c) (x : ↥c.current) :
    x ∈ selectedParents a ↔ x.val ∈ a.val := by
  classical
  exact Finset.mem_subtype

theorem sum_selectedParents {c : Context d} (a : Selection c) (f : c.Event → Int) :
    ∑ x ∈ selectedParents a, f x.val = ∑ x ∈ a.val, f x := by
  classical
  exact Finset.sum_subtype_of_mem f a.property

theorem selectedParents_eq_empty_of_current {c : Context d} (a : Selection c)
    (h : c.current = ∅) : selectedParents a = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x _
  have := x.property
  simp [h] at this

end
end D5.S3.ConceptDynamics.Spacetime.ProductNodes
