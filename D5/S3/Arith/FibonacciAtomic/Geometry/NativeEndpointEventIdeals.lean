/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Membership partial native endpoints and their actual guarded event transitions. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair
import D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
import Mathlib.Data.List.Infix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address readout)
open ActualLeafHistoryRigidity (subtree)
open ActualImageAddressCertificate (replace)
open NativeMaterialRootRecognition (D)
open NativeGuardedLeafRepair (Call run)

/-- Alpha is the root/right birth type; a left child is born beta. -/
def birthAt : Bool → Address → Bool
  | b, [] => b
  | _, c :: p => birthAt c p

/-- Pull membership back along the original address shift. -/
def sectionAt (I : Set Call) (p : Address) : Set Call :=
  {c | c.shift p ∈ I}

/-- Exactly the endpoint's split labels and nontrivial born-alpha promotions. -/
def events : Bool → Source → Finset Call
  | b, .of a => if b && !a then {.promote []} else ∅
  | b, .mul l r =>
      (if b then {.promote []} else ∅) ∪ {.split []} ∪
      (events false l).image (Call.shift [false]) ∪
      (events true r).image (Call.shift [true])

/-- A partial endpoint uses membership only, with no execution or chosen order. -/
noncomputable def partial : Bool → Source → Set Call → Source
  | b, .of a, I => if b && !a then
      if .promote [] ∈ I then .of false else .of true
    else .of a
  | b, .mul l r, I => if .split [] ∈ I then
      .mul (partial false l (sectionAt I [false]))
        (partial true r (sectionAt I [true]))
    else if b then if .promote [] ∈ I then .of false else .of true
    else .of false

/-- Every strict ancestor's creating split has occurred. -/
def Created : Set Call → Address → Prop
  | _, [] => True
  | I, b :: p => .split [] ∈ I ∧ Created (sectionAt I [b]) p

/-- The actual leaf guard, on the unchanged native subtree operation. -/
def Guard : Call → Source → Prop
  | .promote p, u => subtree p u = some (.of true)
  | .split p, u => subtree p u = some (.of false)

/-- The original replacement made by a successful single call. -/
def next : Call → Source → Source
  | .promote p, u => replace u p (.of false)
  | .split p, u => replace u p (.mul (.of false) (.of true))

private theorem shift_append (p q : Address) (c : Call) :
    (c.shift q).shift p = c.shift (p ++ q) := by
  cases c <;> simp [Call.shift, List.append_assoc]

private theorem section_cons (I : Set Call) (b : Bool) (p : Address) :
    sectionAt (sectionAt I [b]) p = sectionAt I (b :: p) := by
  ext c
  simp [sectionAt, shift_append]

private theorem partial_leaf (b a : Bool) (I : Set Call) :
    ∃ x : Bool, partial b (.of a) I = .of x := by
  classical
  cases b <;> cases a <;> simp [partial]
  split_ifs <;> exact ⟨_, rfl⟩

/-- The actual addressed subtree exists precisely after all creating splits.
The subtree itself is the membership-defined local partial endpoint. -/
theorem subtree_partial (t : Source) (p : Address) (v : Source)
    (hp : subtree p t = some v) (b : Bool) (I : Set Call) :
    subtree p (partial b t I) =
      if Created I p then some (partial (birthAt b p) v (sectionAt I p)) else none := by
  classical
  induction p generalizing t b I with
  | nil =>
      have ht : t = v := by simpa [subtree] using hp
      subst v
      have hs : sectionAt I [] = I := by
        ext c
        cases c <;> simp [sectionAt, Call.shift]
      simp [subtree, birthAt, Created, hs]
  | cons c p ih =>
      cases t with
      | of a => simp [subtree] at hp
      | mul l r =>
          by_cases hs : Call.split [] ∈ I
          · cases c
            · simpa [partial, hs, subtree, Created, birthAt, section_cons] using
                ih l (by simpa [subtree] using hp) false (sectionAt I [false])
            · simpa [partial, hs, subtree, Created, birthAt, section_cons] using
                ih r (by simpa [subtree] using hp) true (sectionAt I [true])
          · simp only [partial, hs, ↓reduceIte, Created, false_and, birthAt]
            cases b <;> simp [subtree]
            split_ifs <;> rfl

/-- Local beta/alpha leaf recognition in a partial endpoint. This is a
structural fact about actual constructors, rather than a run assumption. -/
private theorem local_guard (b : Bool) (t : Source) (I : Set Call)
    (hn : t ≠ .of true) :
    (partial b t I = .of true ↔
      b = true ∧ .promote [] ∉ I ∧ (∀ l r, t = .mul l r → .split [] ∉ I)) ∧
    (partial b t I = .of false ↔
      (b = false ∨ .promote [] ∈ I) ∧ (∀ l r, t = .mul l r → .split [] ∉ I)) := by
  classical
  cases t with
  | of a => cases a <;> cases b <;> simp_all [partial]
  | mul l r =>
      cases b <;> by_cases hs : Call.split [] ∈ I <;>
        by_cases hp : Call.promote [] ∈ I <;> simp [partial, hs, hp]

/-- Actual guard/ancestor correspondence for every non-alpha target subtree.
All membership tests are on endpoint labels; no execution defines the cut. -/
theorem guard_ancestor (t : Source) (p : Address) (v : Source)
    (hp : subtree p t = some v) (hn : v ≠ .of true) (b : Bool) (I : Set Call) :
    (Guard (.promote p) (partial b t I) ↔
      Created I p ∧ birthAt b p = true ∧ .promote p ∉ I ∧
        (∀ l r, v = .mul l r → .split p ∉ I)) ∧
    (Guard (.split p) (partial b t I) ↔
      Created I p ∧ (birthAt b p = false ∨ .promote p ∈ I) ∧
        (∀ l r, v = .mul l r → .split p ∉ I)) := by
  classical
  have hs := subtree_partial t p v hp b I
  have hg := local_guard (birthAt b p) v (sectionAt I p) hn
  simp only [Guard, hs]
  by_cases hc : Created I p
  · simp only [hc, ↓reduceIte, Option.some.injEq, true_and]
    simpa [sectionAt, Call.shift] using hg
  · simp [hc]

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals
