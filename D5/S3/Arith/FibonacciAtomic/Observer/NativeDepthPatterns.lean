/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original-prefix locality and exact reached-frontier decomposition of native trees. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)

/-- Only originally present subtrees are transported. Born addresses are excluded. -/
theorem original_present_transport (n : Nat) (a : Address) (u t : Source)
    (present : subtree a u = some t) :
    subtree a (substitution^[n] u) = some (substitution^[n] t) := by
  induction a generalizing u with
  | nil => simpa [subtree] using congrArg (Option.map (substitution^[n])) present
  | cons b a ih =>
      cases u with
      | of c => simp [subtree] at present
      | mul l r =>
          rw [Function.Semiconj₂.iterate
            (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
              fun s t => substitution.map_mul s t) n l r]
          cases b <;> exact ih _ present

/-- Every epoch reply at s depends only on original replies through depth |s|. -/
theorem original_prefix_locality (n : Nat) (s : Address) (u v : Source)
    (same : ∀ a : Address, a.length ≤ s.length → readout a u = readout a v) :
    readout s (substitution^[n] u) = readout s (substitution^[n] v) := by
  induction s generalizing u v with
  | nil =>
      have root := same [] (by simp)
      cases u with
      | of b => cases v with
        | of c => cases b <;> cases c <;> simp_all [readout]
        | mul l r => cases b <;> simp [readout] at root
      | mul l r =>
          cases v with
          | of c => cases c <;> simp [readout] at root
          | mul l' r' =>
              rw [Function.Semiconj₂.iterate
                (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
                  fun s t => substitution.map_mul s t) n l r,
                Function.Semiconj₂.iterate
                (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
                  fun s t => substitution.map_mul s t) n l' r']
              rfl
  | cons b s ih =>
      have root := same [] (by simp)
      cases u with
      | of c => cases v with
        | of e => cases c <;> cases e <;> simp_all [readout]
        | mul l r => cases c <;> simp [readout] at root
      | mul l r =>
          cases v with
          | of c => cases c <;> simp [readout] at root
          | mul l' r' =>
              have left (a : Address) (ha : a.length ≤ s.length) :
                  readout a l = readout a l' := by
                exact same (false :: a) (by simpa using ha)
              have right (a : Address) (ha : a.length ≤ s.length) :
                  readout a r = readout a r' := by
                exact same (true :: a) (by simpa using ha)
              have lt := original_present_transport n [false] (.mul l r) l rfl
              have rt := original_present_transport n [true] (.mul l r) r rfl
              have lt' := original_present_transport n [false] (.mul l' r') l' rfl
              have rt' := original_present_transport n [true] (.mul l' r') r' rfl
              have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              cases b
              · change readout ([false] ++ s) _ = readout ([false] ++ s) _
                rw [app, lt, app, lt']; exact ih l l' left
              · change readout ([true] ++ s) _ = readout ([true] ++ s) _
                rw [app, rt, app, rt']; exact ih r r' right

/-- A depth-zero pattern is one frontier hole. At positive depth it is a
concrete original leaf or an ordered pair of shallower patterns. -/
def Pattern : Nat → Type
  | 0 => Unit
  | d + 1 => Bool ⊕ (Pattern d × Pattern d)

instance patternDecidableEq (d : Nat) : DecidableEq (Pattern d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ d ih => exact inferInstanceAs (DecidableEq (Bool ⊕ (Pattern d × Pattern d)))

instance patternFintype (d : Nat) : Fintype (Pattern d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ d ih => exact inferInstanceAs (Fintype (Bool ⊕ (Pattern d × Pattern d)))

/-- Variables exist at all and only reached depth-d positions. Early leaves
have no variable; the two child frontiers are disjoint positions. -/
def Frontier : {d : Nat} → Pattern d → Type
  | 0, _ => Unit
  | _ + 1, .inl _ => PEmpty
  | _ + 1, .inr p => Frontier p.1 ⊕ Frontier p.2

instance frontierDecidableEq {d : Nat} (p : Pattern d) : DecidableEq (Frontier p) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ d ih => cases p with
    | inl b => exact inferInstanceAs (DecidableEq PEmpty)
    | inr p =>
        letI := ih p.1
        letI := ih p.2
        exact inferInstanceAs (DecidableEq (Frontier p.1 ⊕ Frontier p.2))

instance frontierFintype {d : Nat} (p : Pattern d) : Fintype (Frontier p) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ d ih =>
      cases p with
      | inl b => exact inferInstanceAs (Fintype PEmpty)
      | inr p =>
          letI := ih p.1
          letI := ih p.2
          exact inferInstanceAs (Fintype (Frontier p.1 ⊕ Frontier p.2))

/-- Every valuation uses actual finite nonempty Boolean trees. No inequality
between different variable positions is imposed. -/
def fill : {d : Nat} → (p : Pattern d) → (Frontier p → Source) → Source
  | 0, _, f => f ()
  | _ + 1, .inl b, _ => .of b
  | _ + 1, .inr p, f => .mul (fill p.1 (fun x => f (.inl x)))
      (fill p.2 (fun x => f (.inr x)))

/-- The actual frontier address of a variable position. -/
def frontierAddress : {d : Nat} → (p : Pattern d) → Frontier p → Address
  | 0, _, _ => []
  | _ + 1, .inl _, x => PEmpty.elim x
  | _ + 1, .inr p, .inl x => false :: frontierAddress p.1 x
  | _ + 1, .inr p, .inr x => true :: frontierAddress p.2 x

private def combine {d : Nat} (l r : Σ p : Pattern d, Frontier p → Source) :
    Σ p : Pattern (d+1), Frontier p → Source :=
  ⟨.inr (l.1, r.1), Sum.elim l.2 r.2⟩

/-- Unique pattern together with its actual reached frontier subtrees. -/
def decompose : (d : Nat) → Source → Σ p : Pattern d, Frontier p → Source
  | 0, t => ⟨(), fun _ => t⟩
  | _ + 1, .of b => ⟨.inl b, PEmpty.elim⟩
  | d + 1, .mul l r =>
      combine (decompose d l) (decompose d r)

private theorem fill_decompose (d : Nat) (t : Source) :
    fill (decompose d t).1 (decompose d t).2 = t := by
  induction d generalizing t with
  | zero => rfl
  | succ d ih => cases t with
    | of b => rfl
    | mul l r => simpa only [decompose, combine, fill, Sum.elim_inl, Sum.elim_inr] using congrArg₂ FreeMagma.mul (ih l) (ih r)

private theorem decompose_fill (d : Nat) (p : Pattern d) (f : Frontier p → Source) :
    decompose d (fill p f) = ⟨p, f⟩ := by
  induction d with
  | zero =>
      cases p
      apply Sigma.ext rfl
      apply heq_of_eq
      funext x
      cases x
      rfl
  | succ d ih =>
      cases p with
      | inl b =>
          change (⟨Sum.inl b, PEmpty.elim⟩ : Σ p : Pattern (d+1), Frontier p → Source) = _
          congr 1
          funext x
          exact PEmpty.elim x
      | inr p =>
          rcases p with ⟨l, r⟩
          change combine (decompose d (fill l (fun x => f (.inl x))))
            (decompose d (fill r (fun x => f (.inr x)))) = _
          rw [ih, ih]
          exact congrArg (fun g : Frontier (d := d+1) (Sum.inr (l,r)) → Source =>
            (⟨Sum.inr (l,r), g⟩ : Σ p : Pattern (d+1), Frontier p → Source))
            (funext fun x => by cases x <;> rfl)

/-- Exact decomposition, not a finite sample or a bound on source size. -/
def depthEquiv (d : Nat) : Source ≃ Σ p : Pattern d, Frontier p → Source where
  toFun := decompose d
  invFun x := fill x.1 x.2
  left_inv := fill_decompose d
  right_inv x := decompose_fill d x.1 x.2

/-- Complete finite mixed-epoch histories include repeated and absent replies. -/
abbrev History := List (Nat × Address × Reply)

def Consistent (H : History) (t : Source) : Prop :=
  ∀ e ∈ H, readout e.2.1 (substitution^[e.1] t) = e.2.2

instance consistentDecidable (H : History) (t : Source) : Decidable (Consistent H t) :=
  inferInstanceAs (Decidable (∀ e ∈ H, readout e.2.1 (substitution^[e.1] t) = e.2.2))

/-- Variables name exactly the reached depth-d frontier. Every filling has
those same positions, and the actual subtrees there reconstruct its valuation. -/
theorem frontier_geometry (d : Nat) (p : Pattern d) :
    (∀ x : Frontier p, (frontierAddress p x).length = d) ∧
    (∀ (f : Frontier p → Source) (x : Frontier p),
      subtree (frontierAddress p x) (fill p f) = some (f x)) ∧
    (∀ (f : Frontier p → Source) (a : Address), a.length = d →
      ((subtree a (fill p f)).isSome ↔ ∃ x : Frontier p, frontierAddress p x = a)) := by
  have length : ∀ x : Frontier p, (frontierAddress p x).length = d := by
    induction d with
    | zero => intro x; rfl
    | succ d ih => cases p with
      | inl b => intro x; exact PEmpty.elim x
      | inr p => intro x; cases x <;> simp [frontierAddress, ih]
  have recover : ∀ (f : Frontier p → Source) (x : Frontier p),
      subtree (frontierAddress p x) (fill p f) = some (f x) := by
    clear length
    induction d with
    | zero => intro f x; cases x; rfl
    | succ d ih => cases p with
      | inl b => intro f x; exact PEmpty.elim x
      | inr p => intro f x; cases x <;> simp only [frontierAddress, fill, subtree, ih]
  refine ⟨length, recover, ?_⟩
  clear length recover
  induction d with
  | zero =>
      intro f a ha
      have ae : a = [] := List.length_eq_zero_iff.mp ha
      subst a
      simp [fill, subtree, frontierAddress, Frontier]
  | succ d ih =>
      intro f a ha
      cases a with
      | nil => simp at ha
      | cons b a =>
          have ha' : a.length = d := by simpa using ha
          cases p with
          | inl c => simp [fill, subtree, Frontier, frontierAddress]
          | inr p =>
              cases b
              · simpa [fill, subtree, frontierAddress, Frontier, Sum.exists] using
                  ih p.1 (fun x => f (.inl x)) a ha'
              · simpa [fill, subtree, frontierAddress, Frontier, Sum.exists] using
                  ih p.2 (fun x => f (.inr x)) a ha'

end D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
