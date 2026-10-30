/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalCoordinatePrefix
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Additive finite lookahead recovers original native prefixes from actual power images. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalEffectivePrefix
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeImageSaturationInterface
import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate

/-! Additive native inverse-prefix continuity and finite pattern decoding. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalCoordinatePrefix

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeCompletionPrefixLifting
open CompletionHomogeneousFixedPoints
open ActualImageAddressCertificate (height)
open NativeDepthPatterns (Pattern decompose)

/- The finite terminal heights are taken from the actual source preimages of
   the two image terminals; no rational or regular-tree representation is used. -/
def terminalHeight (s : Nat) : Nat :=
  max (height (substitution^[s] (.of true)))
    (height (substitution^[s] (.of false)))

private theorem source_height_leaf (b : Bool) : height (.of b) = 0 := rfl

private theorem source_height_pair (l r : Source) :
    height (.mul l r) = max (height l) (height r) + 1 := rfl

private theorem finite_prefix_ext (t : Source) (X : CompletionTree)
    (agree : ∀ p : Address, p.length ≤ height t →
      completionReadout p X = readout p t) :
    X = embed t := by
  induction t generalizing X with
  | of b =>
      induction X using tree_cases with
      | leaf_case c =>
          have root := agree [] (by simp [source_height_leaf])
          cases b <;> cases c <;>
            simp [completionReadout, leaf, embed, readout] at root ⊢
      | node_case l r =>
          have root := agree [] (by simp [source_height_leaf])
          cases b <;> simp [completionReadout, leaf, node, embed, readout] at root
  | mul l r ihl ihr =>
      induction X using tree_cases with
      | leaf_case b =>
          have root := agree [] (by simp [source_height_pair])
          cases b <;> simp [completionReadout, leaf, node, embed, readout] at root
      | node_case x y =>
          have left : ∀ p : Address, p.length ≤ height l →
              completionReadout p x = readout p l := by
            intro p hp
            have h := agree (false :: p) (by
              simp only [List.length_cons, source_height_pair]
              omega)
            simpa [completionReadout, node, embed, readout] using h
          have right : ∀ p : Address, p.length ≤ height r →
              completionReadout p y = readout p r := by
            intro p hp
            have h := agree (true :: p) (by
              simp only [List.length_cons, source_height_pair]
              omega)
            simpa [completionReadout, node, embed, readout] using h
          exact congrArg₂ node (ihl x left) (ihr y right)

private theorem terminal_prefix_ext (s : Nat) (b : Bool) (X : CompletionTree)
    (agree : ∀ p : Address, p.length ≤ terminalHeight s →
      completionReadout p X = completionReadout p (rho^[s] (leaf b))) :
    X = rho^[s] (leaf b) := by
  let t : Source := substitution^[s] (.of b)
  have image : embed t = rho^[s] (leaf b) := by
    simpa [t, embed] using (iterate_embed s (.of b)).symm
  have hx : X = embed t := by
    apply finite_prefix_ext t X
    intro p hp
    have bound : height t ≤ terminalHeight s := by
      dsimp [t, terminalHeight]
      cases b with
      | false => exact Nat.le_max_right _ _
      | true => exact Nat.le_max_left _ _
    have h := agree p (hp.trans bound)
    rw [← image] at h
    exact h.trans (embed_readout p t)
  exact hx.trans image

private theorem root_recovery (s h : Nat) (U V : CompletionTree)
    (agree : ∀ p : Address, p.length ≤ h + terminalHeight s →
      completionReadout p (rho^[s] U) = completionReadout p (rho^[s] V)) :
    completionReadout [] U = completionReadout [] V := by
  induction U using tree_cases with
  | leaf_case b =>
      induction V using tree_cases with
      | leaf_case c =>
          have terminal' : rho^[s] (leaf c) = rho^[s] (leaf b) :=
            terminal_prefix_ext s b (rho^[s] (leaf c)) (by
            intro p hp
            exact (agree p (by omega)).symm)
          have terminal : rho^[s] (leaf b) = rho^[s] (leaf c) := terminal'.symm
          have leaves : leaf b = leaf c := (rho_injective.iterate s) terminal
          have root := congrArg (completionReadout []) leaves
          simpa [completionReadout, leaf] using root
      | node_case l r =>
          have terminal' : rho^[s] (node l r) = rho^[s] (leaf b) :=
            terminal_prefix_ext s b (rho^[s] (node l r)) (by
            intro p hp
            exact (agree p (by omega)).symm)
          have terminal : rho^[s] (leaf b) = rho^[s] (node l r) := terminal'.symm
          have impossible : leaf b = node l r := (rho_injective.iterate s) terminal
          have root := congrArg (completionReadout []) impossible
          cases b <;> simp [completionReadout, leaf, node] at root
  | node_case l r =>
      induction V using tree_cases with
      | leaf_case b =>
          have terminal' : rho^[s] (node l r) = rho^[s] (leaf b) :=
            terminal_prefix_ext s b (rho^[s] (node l r)) (by
            intro p hp
            exact agree p (by omega))
          have terminal : rho^[s] (leaf b) = rho^[s] (node l r) := terminal'.symm
          have impossible : leaf b = node l r := (rho_injective.iterate s) terminal
          have root := congrArg (completionReadout []) impossible
          cases b <;> simp [completionReadout, leaf, node] at root
      | node_case x y =>
          rfl

/- Inclusive image agreement through h+H_s is enough for all original replies
   through h. The recursive branch consumes one level on each side, so H_s is
   added once at the root rather than once per ancestor. -/
theorem inverse_prefix_agreement (s h : Nat) (U V : CompletionTree)
    (agree : ∀ p : Address, p.length ≤ h + terminalHeight s →
      completionReadout p (rho^[s] U) = completionReadout p (rho^[s] V)) :
    ∀ p : Address, p.length ≤ h →
      completionReadout p U = completionReadout p V := by
  induction h generalizing U V with
  | zero =>
      intro p hp
      have empty : p = [] := by simpa using hp
      subst p
      exact root_recovery s 0 U V (by simpa using agree)
  | succ h ih =>
      have root := root_recovery s (h + 1) U V agree
      intro p hp
      cases p with
      | nil => exact root
      | cons b p =>
          have tail : p.length ≤ h := by
            simp only [List.length_cons] at hp
            omega
          cases U using tree_cases with
          | leaf_case c =>
              cases V using tree_cases with
              | leaf_case d => simp [completionReadout, leaf]
              | node_case l r => cases c <;> simp [completionReadout, leaf, node] at root
          | node_case l r =>
              cases V using tree_cases with
              | leaf_case c => cases c <;> simp [completionReadout, leaf, node] at root
              | node_case x y =>
                  cases b with
                  | false =>
                      have child := ih l x
                        (fun q hq => by
                          have ha := agree (false :: q) (by simp; omega)
                          rw [iterate_node, iterate_node] at ha
                          simpa [completionReadout, node] using ha) p tail
                      simpa [completionReadout, node] using child
                  | true =>
                      have child := ih r y
                        (fun q hq => by
                          have ha := agree (true :: q) (by simp; omega)
                          rw [iterate_node, iterate_node] at ha
                          simpa [completionReadout, node] using ha) p tail
                      simpa [completionReadout, node] using child

/-- Compare a finite terminal with a finite image pattern. Only the addresses
of the finite terminal are visited, even when the supplied pattern is deeper. -/
def terminalMatch : (d : Nat) → Source → Pattern d → Bool
  | 0, _, _ => false
  | _ + 1, .of b, .inl c => b == c
  | d + 1, .mul l r, .inr (x, y) =>
      terminalMatch d l x && terminalMatch d r y
  | _ + 1, _, _ => false

private theorem terminal_match_cutoff (t : Source) (d : Nat) (X : CompletionTree)
    (deep : height t < d) :
    terminalMatch d t (cutoff d X) = true ↔ X = embed t := by
  induction t generalizing d X with
  | of b =>
      cases d with
      | zero => omega
      | succ d =>
          cases X using tree_cases with
          | leaf_case c =>
              change (b == c) = true ↔ leaf c = leaf b
              rw [beq_iff_eq]
              constructor
              · intro eq; rw [eq]
              · intro eq
                have root := congrArg (completionReadout []) eq
                cases b <;> cases c <;> simp [completionReadout, leaf] at root ⊢
          | node_case l r =>
              have ne : node l r ≠ embed (.of b) := by
                intro eq
                have root := congrArg (completionReadout []) eq
                cases b <;> simp [completionReadout, embed, leaf, node] at root
              change false = true ↔ node l r = embed (.of b)
              simpa only [Bool.false_eq_true, false_iff] using ne
  | mul l r ihl ihr =>
      cases d with
      | zero => omega
      | succ d =>
          have dl : height l < d := by simp only [source_height_pair] at deep; omega
          have dr : height r < d := by simp only [source_height_pair] at deep; omega
          cases X using tree_cases with
          | leaf_case b =>
              have ne : leaf b ≠ embed (.mul l r) := by
                intro eq
                have root := congrArg (completionReadout []) eq
                cases b <;> simp [completionReadout, embed, leaf, node] at root
              change false = true ↔ leaf b = embed (.mul l r)
              simpa only [Bool.false_eq_true, false_iff] using ne
          | node_case x y =>
              change (terminalMatch d l (cutoff d x) &&
                terminalMatch d r (cutoff d y)) = true ↔
                node x y = node (embed l) (embed r)
              rw [Bool.and_eq_true, ihl d x dl, ihr d y dr]
              exact ⟨fun h => congrArg₂ node h.1 h.2, fun h => node_inj h⟩

private theorem image_terminal_match (s d : Nat) (b : Bool) (X : CompletionTree) :
    terminalMatch (terminalHeight s + (d + 1)) (substitution^[s] (.of b))
      (cutoff (terminalHeight s + (d + 1)) (rho^[s] X)) = true ↔ X = leaf b := by
  have bound : height (substitution^[s] (.of b)) ≤ terminalHeight s := by
    cases b with
    | false => exact Nat.le_max_right _ _
    | true => exact Nat.le_max_left _ _
  rw [terminal_match_cutoff _ _ _ (by omega)]
  have image : embed (substitution^[s] (.of b)) = rho^[s] (leaf b) := by
    simpa [embed] using (iterate_embed s (.of b)).symm
  rw [image]
  exact (rho_injective.iterate s).eq_iff

/-- A total finite decoder. Off-image patterns receive an arbitrary fallback;
correctness is asserted only for prefixes of actual native images. -/
def decodePrefix (s : Nat) : (d : Nat) → Pattern (terminalHeight s + d) → Pattern d
  | 0, _ => ()
  | d + 1, P =>
      if terminalMatch (terminalHeight s + (d + 1)) (substitution^[s] (.of true)) P then
        .inl true
      else if terminalMatch (terminalHeight s + (d + 1)) (substitution^[s] (.of false)) P then
        .inl false
      else match P with
        | .inl b => .inl b
        | .inr (l, r) => .inr (decodePrefix s d l, decodePrefix s d r)

/-- The decoder recovers every finite original prefix, including those of
arbitrary non-rational completed trees, from finite actual-image data. -/
theorem decode_prefix_correct (s d : Nat) (X : CompletionTree) :
    decodePrefix s d (cutoff (terminalHeight s + d) (rho^[s] X)) = cutoff d X := by
  induction d generalizing X with
  | zero => rfl
  | succ d ih =>
      cases X using tree_cases with
      | leaf_case b =>
          cases b with
          | false =>
              have yes := (image_terminal_match s d false (leaf false)).mpr rfl
              have no : terminalMatch (terminalHeight s + (d + 1))
                  (substitution^[s] (.of true))
                  (cutoff (terminalHeight s + (d + 1)) (rho^[s] (leaf false))) = false := by
                cases hm : terminalMatch _ _ _ with
                | false => rfl
                | true =>
                    have bad := (image_terminal_match s d true (leaf false)).mp hm
                    have root := congrArg (completionReadout []) bad
                    simp [completionReadout, leaf] at root
              simp only [decodePrefix, no, Bool.false_eq_true, ↓reduceIte, yes]
              rfl
          | true =>
              have yes := (image_terminal_match s d true (leaf true)).mpr rfl
              simp only [decodePrefix, yes, ↓reduceIte]
              rfl
      | node_case l r =>
          have no (b : Bool) : terminalMatch (terminalHeight s + (d + 1))
              (substitution^[s] (.of b))
              (cutoff (terminalHeight s + (d + 1)) (rho^[s] (node l r))) = false := by
            cases hm : terminalMatch _ _ _ with
            | false => rfl
            | true =>
                have bad := (image_terminal_match s d b (node l r)).mp hm
                have root := congrArg (completionReadout []) bad
                cases b <;> simp [completionReadout, leaf, node] at root
          simp only [decodePrefix, no, Bool.false_eq_true, ↓reduceIte]
          rw [iterate_node]
          change Sum.inr (decodePrefix s d (cutoff (terminalHeight s + d) (rho^[s] l)),
            decodePrefix s d (cutoff (terminalHeight s + d) (rho^[s] r))) =
              Sum.inr (cutoff d l, cutoff d r)
          rw [ih l, ih r]

#print axioms inverse_prefix_agreement
#print axioms decode_prefix_correct

end D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalCoordinatePrefix
