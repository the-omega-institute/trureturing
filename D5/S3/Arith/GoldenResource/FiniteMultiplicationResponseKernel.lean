/- GID: D5/S3/Arith/GoldenResource/FiniteMultiplicationResponseKernel
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/FiniteMultiplicationResponseKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite multiplication responses separate squarefree states and classify other states by truncated remaining capacities. -/

import D5.S0.Rewriting.GuardedBoxPaths
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Int.Defs

set_option autoImplicit false

namespace D5.S3.Arith.GoldenResource.FiniteMultiplicationResponseKernel

open D5.S0.Rewriting.GuardedBoxPaths

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- A state is a natural coordinate vector bounded by its capacity vector. -/
abbrev State (A : P → ℕ) := {a : P → ℕ // ∀ p, a p ≤ A p}

/-- A located state records both its capacity vector and its bounded coordinates. -/
abbrev Located (P : Type*) := Σ A : P → ℕ, {a : P → ℕ // ∀ p, a p ≤ A p}

/-- A squarefree coordinate vector has every coordinate at most one. -/
def SF (a : P → ℕ) : Prop := ∀ p, a p ≤ 1

/-- Squarefreeness of a finite coordinate vector is decidable. -/
instance (a : P → ℕ) : Decidable (SF a) :=
  inferInstanceAs (Decidable (∀ p, a p ≤ 1))

/-- The signed readout is the parity sign on squarefree vectors and zero otherwise. -/
def mu (a : P → ℕ) : ℤ := if SF a then (-1 : ℤ) ^ (∑ p, a p) else 0

/-- Remaining capacity is the coordinatewise natural difference from the capacity. -/
def remaining (A a : P → ℕ) : P → ℕ := fun p => A p - a p

/-- The finite horizon truncates each remaining capacity at the horizon. -/
def truncRemaining (A a : P → ℕ) (h : ℕ) : P → ℕ :=
  fun p => min (remaining A a p) h

/-- A word returns its endpoint readout on success and the distinct failure value otherwise. -/
def response (x : Located P) (w : List (Instruction P)) : Option ℤ :=
  (eval x.1 x.2.val w).map mu

/-- Multiplication words increase the coordinate named by each letter. -/
def plusAllObservation (x : Located P) : List P → Option ℤ :=
  fun w => response x (w.map (fun p => (p, true)))

/-- A finite observation records responses to every multiplication word within its horizon. -/
def plusObservation (h : ℕ) (x : Located P) : {w : List P // w.length ≤ h} → Option ℤ :=
  fun w => plusAllObservation x w.val

/-- Two located states are equivalent when their finite multiplication observations agree. -/
def EqPlus (A : P → ℕ) (a : State A) (B : P → ℕ) (b : State B) (h : ℕ) : Prop :=
  (Setoid.ker (plusObservation (P := P) h)).r ⟨A, a⟩ ⟨B, b⟩

end D5.S3.Arith.GoldenResource.FiniteMultiplicationResponseKernel
