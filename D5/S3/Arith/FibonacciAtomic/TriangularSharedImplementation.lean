/- GID: D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/TriangularSharedImplementation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Immediate-output sharing for every legal stationary triangular table. -/

import D5.S3.Arith.FibonacciAtomic.TriangularPathNormalization
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Bernoulli

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.TriangularSharedImplementation

open scoped BigOperators
open TriangularPathNormalization

/-- A fixed action at every aggregate state, including zero residual states. -/
structure Table (m : ℕ) where
  action : State → Action
  legal : ∀ s, 0 < s.e → s.r < s.e → s.e ≤ m → Legal m s (action s)

/-- The original slot coordinates e, r, k; empty Fin r removes zero residual slots. -/
def Slot (m : ℕ) := Σ e : Fin (m + 1), Σ r : Fin e.val, Fin r.val

/-- The aggregate state of an original slot. -/
def aggregate {m : ℕ} (s : Slot m) : State := ⟨s.2.1.val, s.1.val⟩

/-- Slots with the same one-bit ordered terminal pair can share a vertex. -/
def Immediate {m : ℕ} (s : Slot m) : Prop :=
  s.1.val ≤ 2 * s.2.1.val ∧ s.2.2.val < s.1.val / 2

/-- Shared one-bit vertices and all remaining singleton slots. -/
def SharedActive (m : ℕ) := Fin (m / 2) ⊕ {s : Slot m // ¬Immediate s}

local notation "Original" m => Slot m ⊕ Fin m
local notation "Shared" m => SharedActive m ⊕ Fin m

/-- Activities have no terminal label; distinct terminals retain their own labels. -/
def color {m : ℕ} {A : Type} : A ⊕ Fin m → Option (Fin m)
  | .inl _ => none
  | .inr i => some i

/-- The source root has coordinates (r,e,k)=(1,m,0). -/
def root (m : ℕ) (hm : 2 ≤ m) : Original m :=
  .inl ⟨⟨m, by omega⟩, ⟨⟨1, by omega⟩, ⟨0, by omega⟩⟩⟩

/-- Ordered output count and the successor prescribed by the original column. -/
def outputCount (a : Action) (e : ℕ) : ℕ :=
  match a with
  | .one => e
  | .zero h => h

/-- Label at position z in the ordered output list, represented with zero-based labels. -/
def outputLabel (a : Action) (e z : ℕ) : ℕ :=
  match a with
  | .one => z
  | .zero h => e - h + z

/-- Every active edge consumes one bit; terminal loops are absorbing extensions. -/
def originalStep {m : ℕ} (f : Table m) : Original m → Fin 2 → Original m
  | .inr i, _ => .inr i
  | .inl s, u => by
    let a := f.action (aggregate s)
    let z := 2 * s.2.2.val + u.val
    let q := outputCount a s.1.val
    have hl := f.legal (aggregate s) (by have H := s.2.1.isLt; omega)
      s.2.1.isLt (by have H := s.1.isLt; omega)
    have hz : z < 2 * s.2.1.val := by
      have H := s.2.2.isLt
      have H' := u.isLt
      dsimp [z]
      omega
    if h : z < q then
      exact .inr ⟨outputLabel a s.1.val z, by
        cases ha : a with
        | one => simpa [q, outputCount, ha, outputLabel] using (Nat.lt_of_lt_of_le h hl.2.2.1)
        | zero h' =>
          have H : 2 * s.2.1.val < s.1.val ∧ h' ≤ 2 * s.2.1.val := by
            simpa [Legal, aggregate, a, ha] using hl.2.2.2
          simp only [outputLabel, ha]
          dsimp [q] at h
          simp only [outputCount, ha] at h
          have He := hl.2.2.1
          dsimp [aggregate] at He
          omega⟩
    else
      exact .inl ⟨⟨(successor (aggregate s) a).e, by
        cases ha : a <;> simp [successor, ha, aggregate] <;> omega⟩,
        ⟨⟨(successor (aggregate s) a).r, by
          cases ha : a with
          | one =>
            have H : s.1.val ≤ 2 * s.2.1.val := by
              simpa [Legal, aggregate, a, ha] using hl.2.2.2
            simp [successor, ha, aggregate]
            have Hr := s.2.1.isLt
            omega
          | zero h' =>
            have H : 2 * s.2.1.val < s.1.val ∧ h' ≤ 2 * s.2.1.val := by
              simpa [Legal, aggregate, a, ha] using hl.2.2.2
            simp [successor, ha, aggregate]
            omega⟩,
          ⟨z - q, by
            cases ha : a with
            | one =>
              have H : s.1.val ≤ 2 * s.2.1.val := by
                simpa [Legal, aggregate, a, ha] using hl.2.2.2
              simp [successor, ha, aggregate]
              dsimp [q] at h ⊢
              simp only [outputCount, ha] at h ⊢
              omega
            | zero h' =>
              have H : 2 * s.2.1.val < s.1.val ∧ h' ≤ 2 * s.2.1.val := by
                simpa [Legal, aggregate, a, ha] using hl.2.2.2
              simp [successor, ha, aggregate]
              dsimp [q] at h ⊢
              simp only [outputCount, ha] at h ⊢
              omega⟩⟩⟩

/-- The projection merges precisely the immediate slots of a fixed k. -/
def projection {m : ℕ} : Original m → Shared m
  | .inr i => .inr i
  | .inl s => by
    letI : Decidable (Immediate s) := inferInstanceAs
      (Decidable (s.1.val ≤ 2 * s.2.1.val ∧ s.2.2.val < s.1.val / 2))
    exact if h : Immediate s then .inl (.inl ⟨s.2.2.val, by
      have He := s.1.isLt
      have Hk := h.2
      omega⟩) else .inl (.inr ⟨s, h⟩)

/-- Shared immediate vertices output their ordered pair; singletons use the projected successor. -/
def sharedStep {m : ℕ} (f : Table m) : Shared m → Fin 2 → Shared m
  | .inr i, _ => .inr i
  | .inl (.inl k), u => .inr ⟨2 * k.val + u.val, by
      have H := k.isLt
      have H' := u.isLt
      omega⟩
  | .inl (.inr s), u => projection (originalStep f (.inl s.val) u)

/-- The state after a finite prefix of an infinite bit stream. -/
def trace {A : Type} (δ : A → Fin 2 → A) (s : A) (ω : ℕ → Fin 2) (n : ℕ) : A :=
  (List.ofFn (fun j : Fin n => ω j.val)).foldl δ s

/-- First terminal label and consumed length, including a terminal initial state at length zero. -/
def FirstStop {m : ℕ} {A : Type} (δ : A → Fin 2 → A) (c : A → Option (Fin m))
    (s : A) (ω : ℕ → Fin 2) (i : Fin m) (n : ℕ) : Prop :=
  c (trace δ s ω n) = some i ∧ ∀ j < n, c (trace δ s ω j) = none

/-- Paid bits among a prefix: precisely the edges whose source is still active. -/
def charged {m : ℕ} {A : Type} (δ : A → Fin 2 → A) (c : A → Option (Fin m))
    (s : A) (ω : ℕ → Fin 2) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun j => c (trace δ s ω j) = none)).card

/-- Nontermination means every prefix is still active. -/
def Nonstop {m : ℕ} {A : Type} (δ : A → Fin 2 → A) (c : A → Option (Fin m))
    (s : A) (ω : ℕ → Fin 2) : Prop := ∀ n, c (trace δ s ω n) = none

/-- Activity states obtainable from the root by a finite input word. -/
def ReachableActive {m : ℕ} (δ : Shared m → Fin 2 → Shared m) (s : Shared m) :=
  {a : SharedActive m // ∃ w : List (Fin 2), w.foldl δ s = .inl a}

/-- The general sufficient activity bound; subtraction removes all immediate slots. -/
def bound (m : ℕ) : ℕ :=
  m * (m - 1) * (m + 1) / 6 - (∑ e ∈ Finset.range (m + 1), (e / 2) ^ 2) + m / 2

end D5.S3.Arith.FibonacciAtomic.TriangularSharedImplementation
