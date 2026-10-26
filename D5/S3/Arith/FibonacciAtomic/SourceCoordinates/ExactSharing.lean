/- GID: D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact rooted fringe sharing and counted pure evaluation of Fibonacci sources. -/

import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap
import D5.S3.Arith.FibonacciAtomic.CliffordLeafOrbit

/-! Exact sharing retains complete ordered subtrees and evaluates a pure fold by a counted loop. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.Arith.FibonacciAtomic.SourceCoordinates.ExactSharing

open GenealogicalFiberTransport (Source substitution composition)
open Geometry.AncestorAreaInstability (T)

/-- All nodes in the expanded ordered tree, including its leaves. -/
def expandedNodes : Source → ℕ
  | .of _ => 1
  | .mul s t => expandedNodes s + expandedNodes t + 1

/-- Distinct rooted fringe subtrees; equality retains labels, ports and brackets. -/
def fringes : Source → Finset Source
  | .of b => {.of b}
  | .mul s t => insert (.mul s t) (fringes s ∪ fringes t)

/-- One binary call updates two consecutive values and increments its call counter. -/
def evalStep {A : Type u} (μ : A → A → A) (s : A × A × ℕ) : A × A × ℕ :=
  (s.2.1, μ s.2.1 s.1, s.2.2 + 1)

/-- Shared evaluation from supplied leaf values, returning the value and binary-call count. -/
def sharedEval {A : Type u} (μ : A → A → A) (a b : A) (n : ℕ) : A × ℕ :=
  if n = 0 then (a, 0) else
    let s := (evalStep μ)^[n - 1] (a, b, 0)
    (s.2.1, s.2.2)

private theorem recurrence (n : ℕ) : T (n + 2) = .mul (T (n + 1)) (T n) := by
  have h := (SourceTransportCentralizer.source_transport_centralizer.1 (T n)).mpr ⟨n, rfl⟩
  simpa only [T, Function.iterate_succ_apply'] using h

private theorem leaf_count (n : ℕ) : (T n).length = Nat.fib (n + 1) := by
  simpa only [T, composition, FreeMagma.length, Nat.mul_one, Nat.mul_zero, Nat.add_zero] using
    NativeRotationDepthGap.iterate_length (.of true) n

private theorem expanded_count (t : Source) : expandedNodes t = 2 * t.length - 1 := by
  induction t with
  | of b => rfl
  | mul s t hs ht =>
    have hsp := s.length_pos
    have htp := t.length_pos
    simp only [expandedNodes, FreeMagma.length, hs, ht]
    omega

private theorem orbit_injective : Function.Injective T := by
  have primitive : IntrinsicSubstitutionCoordinates.Primitive (.of true) := by
    rintro ⟨x, hx⟩
    exact IntrinsicSubstitutionCoordinates.no_alpha x hx
  intro m n he
  have hm := (IntrinsicSubstitutionCoordinates.intrinsic_coordinates (T m)).2.2.2.1
    (.of true) m primitive rfl
  have hn := (IntrinsicSubstitutionCoordinates.intrinsic_coordinates (T m)).2.2.2.1
    (.of true) n primitive he.symm
  exact hm.1.trans hn.1.symm

private theorem fringes_orbit (n : ℕ) :
    fringes (T (n + 2)) = (Finset.range (n + 3)).image T := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [recurrence]
    decide
  | one =>
    rw [recurrence, recurrence]
    decide
  | more n hn hn1 =>
    rw [recurrence (n + 2)]
    simp only [fringes]
    rw [show n + 2 + 1 = n + 1 + 2 by omega]
    -- The larger child contains every fringe of the smaller child.
    rw [hn1, hn]
    rw [Finset.union_eq_left.mpr (Finset.image_subset_image
      (Finset.range_mono (by omega : n + 3 ≤ n + 1 + 3)))]
    have hnew := Finset.range_add_one (n := n + 1 + 3)
    rw [show n + 2 + 3 = (n + 1 + 3) + 1 by omega, hnew, Finset.image_insert]
    rw [← recurrence (n + 2)]

private theorem fringe_description (n : ℕ) :
    fringes (T n) = if n < 2 then {T n} else (Finset.range (n + 1)).image T := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => simpa only [Nat.not_lt.mpr (by omega : 2 ≤ n + 2), ite_false,
        Nat.add_assoc] using fringes_orbit n

private theorem fringe_card (n : ℕ) :
    (fringes (T n)).card = if n < 2 then 1 else n + 1 := by
  rw [fringe_description]
  split_ifs with h
  · exact Finset.card_singleton _
  · rw [Finset.card_image_of_injective _ orbit_injective, Finset.card_range]

private theorem eval_loop {A : Type u} (μ : A → A → A) (E : Source → A)
    (hE : ∀ s t, E (.mul s t) = μ (E s) (E t)) (k : ℕ) :
    (evalStep μ)^[k] (E (.of true), E (.of false), 0) = (E (T k), E (T (k + 1)), k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [evalStep, recurrence, hE]

private theorem evaluation {A : Type u} (μ : A → A → A) (E : Source → A)
    (hE : ∀ s t, E (.mul s t) = μ (E s) (E t)) (n : ℕ) :
    sharedEval μ (E (.of true)) (E (.of false)) n = (E (T n), n - 1) := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [sharedEval, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
      eval_loop μ E hE]

/-- Exact expanded and shared sizes, the complete fringe set, and a counted pure interpreter.
The counter records binary calls with supplied leaf values, not bit time or output size. -/
theorem exact_sharing :
    (∀ n : ℕ,
      composition (T n) = GraftAffineClosure.atomicBlock n ∧
      (T n).length = Nat.fib (n + 1) ∧
      expandedNodes (T n) = 2 * Nat.fib (n + 1) - 1 ∧
      (n < 2 → fringes (T n) = {T n} ∧ (fringes (T n)).card = 1) ∧
      (2 ≤ n → fringes (T n) = (Finset.range (n + 1)).image T ∧
        (fringes (T n)).card = n + 1)) ∧
    (∀ (A : Type u) (μ : A → A → A) (E : Source → A),
      (∀ s t, E (.mul s t) = μ (E s) (E t)) → ∀ n : ℕ,
        sharedEval μ (E (.of true)) (E (.of false)) n = (E (T n), n - 1)) := by
  constructor
  · intro n
    refine ⟨CliffordLeafOrbit.result.{0}.1 n, leaf_count n,
      (expanded_count (T n)).trans (congrArg (fun k => 2 * k - 1) (leaf_count n)),
      ?_, ?_⟩
    · intro hn
      exact ⟨by rw [fringe_description, if_pos hn], by rw [fringe_card, if_pos hn]⟩
    · intro hn
      exact ⟨by rw [fringe_description, if_neg (Nat.not_lt.mpr hn)],
        by rw [fringe_card, if_neg (Nat.not_lt.mpr hn)]⟩
  · intro A μ E hE n
    exact evaluation μ E hE n

#print axioms exact_sharing

end D5.S3.Arith.FibonacciAtomic.SourceCoordinates.ExactSharing
