/- GID: D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CarryGraphEmbedding
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Canonical minimum-anchor embedding of positive real laws in the original carry graph. -/

import D5.S3.Arith.FibonacciAtomic.DyadicSupportLines
import Mathlib.Analysis.Real.OfDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding

open scoped BigOperators

/-- The integer residual width and the size of the minimum-anchor equality group. -/
structure State where
  r : ℤ
  e : ℤ

/-- Parameters of one column: anchor bit, departing equal labels, larger one-labels. -/
structure Action where
  b : ℤ
  h : ℤ
  c : ℤ

/-- All states of the original carry graph, including unreachable states. -/
def IsState (m : ℕ) (s : State) : Prop :=
  0 ≤ s.r ∧ s.r ≤ (m : ℤ) - 1 ∧ 1 ≤ s.e ∧ s.e ≤ m

/-- A single continuing root cylinder and all labels in the equality group. -/
def root (m : ℕ) : State := ⟨1, m⟩

/-- The number of labels with a one in the next column. -/
def ones (s : State) (a : Action) : ℤ :=
  if a.b = 1 then s.e + a.c else a.h + a.c

/-- The residual recurrence and the removal of departing equality-group labels. -/
def successor (s : State) (a : Action) : State :=
  ⟨2 * s.r - ones s a, s.e - a.h⟩

/-- Exactly the two action rows, together with the successor's state bounds. -/
def Legal (m : ℕ) (s : State) (a : Action) : Prop :=
  IsState m s ∧
    ((a.b = 1 ∧ a.h = 0 ∧ 0 ≤ a.c ∧ a.c ≤ (m : ℤ) - s.e) ∨
      (a.b = 0 ∧ 0 ≤ a.h ∧ a.h ≤ s.e - 1 ∧
        0 ≤ a.c ∧ a.c ≤ (m : ℤ) - s.e)) ∧
    IsState m (successor s a)

/-- An infinite sequence of states and column actions; column zero produces bit one. -/
structure Path where
  state : ℕ → State
  action : ℕ → Action

/-- A path begins at the root and takes a legal action at every depth. -/
def IsRootPath (m : ℕ) (γ : Path) : Prop :=
  γ.state 0 = root m ∧ ∀ d,
    Legal m (γ.state d) (γ.action d) ∧
      γ.state (d + 1) = successor (γ.state d) (γ.action d)

/-- The anchor value, with the first column bit weighted by one half. -/
noncomputable def anchorValue (γ : Path) : ℝ :=
  ∑' d : ℕ, (γ.action d).b / (2 : ℝ) ^ (d + 1)

/-- The whole-column residual tail cost, including the root term. -/
noncomputable def pathCost (γ : Path) : ℝ :=
  ∑' d : ℕ, (γ.state d).r / (2 : ℝ) ^ d

end D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding
