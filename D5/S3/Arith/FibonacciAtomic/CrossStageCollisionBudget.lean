/- GID: D5/S3/Arith/FibonacciAtomic/CrossStageCollisionBudget
   generality: G
   mirror-B: none(waiver:stage-A-content)
   mirror-E: none(waiver:stage-A-content)
   anchors: []
   utility: none
   digest: Integer affine fibres and endpoint minimization for the cross-stage budget.
-/

import D5.S1.Scale.Fibonacci
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CrossStageCollisionBudget

/- The three-step composition matrix from the source text.  The definitions
   below keep the stage notation available to later completion work. -/
def S (v : ℤ × ℤ) : ℤ × ℤ :=
  (v.1 + 2 * v.2, 2 * v.1 + 3 * v.2)

def A (ell : ℕ) : ℤ := Nat.fib (3 * ell + 3)

def B (ell : ℕ) : ℤ := Nat.fib (3 * ell + 4)

def v (ell : ℕ) : ℤ := B ell - A ell

def stageRow (ell : ℕ) (x : ℤ × ℤ) : ℤ := A ell * x.1 + B ell * x.2

def sourceSize (x : ℤ × ℤ) : ℤ := x.1 + x.2

def N (j : ℕ) : ℤ := Nat.fib (3 * j + 1)

def fibrePoint (ell : ℕ) (a b z : ℤ) : ℤ × ℤ :=
  (a + z * B ell, b - z * A ell)

def conePoint (r s : ℤ) (x : ℤ × ℤ) : Prop :=
  0 < s ∧ r * x.2 ≤ s * x.1 ∧ s * x.1 ≤ (s + r) * x.2

def affineSum (ell : ℕ) (a b z : ℤ) : ℤ :=
  sourceSize (fibrePoint ell a b z)

theorem stage_row_fibre (ell : ℕ) (a b z : ℤ) :
    stageRow ell (fibrePoint ell a b z) = stageRow ell (a, b) := by
  dsimp [stageRow, fibrePoint]
  ring

theorem affine_sum_formula (ell : ℕ) (a b z : ℤ) :
    affineSum ell a b z = a + b + z * v ell := by
  dsimp [affineSum, sourceSize, fibrePoint, v]
  ring

theorem affine_sum_strictMono
    (ell : ℕ) (hA : A ell < B ell) (a b z₁ z₂ : ℤ) (hz : z₁ < z₂) :
    affineSum ell a b z₁ < affineSum ell a b z₂ := by
  rw [affine_sum_formula, affine_sum_formula]
  have hv : 0 < v ell := by
    dsimp [v]
    omega
  nlinarith

/- This is the content part of the Stage-A witness.  It says that once the
   strict source-exclusion bound has been established for the high-stage
   sources, the affine fibre's licensed endpoint is the unique least-budget
   point.  The endpoint hypotheses are deliberately explicit: they are the
   exact obligations still missing from the frozen library. -/
theorem CrossStageSourceExclusionAndEndpointMinimization
    (ell k d : ℕ) (hA : A ell < B ell)
    (r s : ℤ) (hs : 0 < s)
    (a b τ : ℤ)
    (hτ : 0 ≤ τ)
    (hendpoint : conePoint r s (fibrePoint ell a b (-τ)))
    (hminimal : ∀ z : ℤ, conePoint r s (fibrePoint ell a b z) → -τ ≤ z)
    (hsource : ∀ (x y : ℤ × ℤ),
      0 ≤ x.1 → 0 ≤ x.2 → 0 ≤ y.1 → 0 ≤ y.2 →
      y ≠ (0, 0) → y ≠ (1, 0) →
      stageRow ell x = stageRow (ell + d) y →
      N d < sourceSize x) :
    (∀ (x y : ℤ × ℤ),
      0 ≤ x.1 → 0 ≤ x.2 → 0 ≤ y.1 → 0 ≤ y.2 →
      y ≠ (0, 0) → y ≠ (1, 0) →
      stageRow ell x = stageRow (ell + d) y →
      N d < sourceSize x) ∧
    (∀ z : ℤ, conePoint r s (fibrePoint ell a b z) →
      affineSum ell a b (-τ) ≤ affineSum ell a b z) ∧
    (∀ z : ℤ, conePoint r s (fibrePoint ell a b z) →
      affineSum ell a b (-τ) = affineSum ell a b z → z = -τ) := by
  have hstrict : 0 < v ell := by
    dsimp [v]
    omega
  refine ⟨hsource, ?_, ?_⟩
  · intro z hz
    have hz' : -τ ≤ z := hminimal z hz
    rw [affine_sum_formula, affine_sum_formula]
    nlinarith
  · intro z hz heq
    have hz' : -τ ≤ z := hminimal z hz
    rw [affine_sum_formula, affine_sum_formula] at heq
    have : z ≤ -τ := by nlinarith
    exact le_antisymm this hz'

/- The exact source-exclusion statement is retained as an open predicate until
   the Fibonacci-indexed gap estimate is supplied. -/
def CrossStageSourceExclusion (ell k d : ℕ) : Prop :=
  ∀ (x y : ℤ × ℤ),
    0 ≤ x.1 → 0 ≤ x.2 → 0 ≤ y.1 → 0 ≤ y.2 →
    y ≠ (0, 0) → y ≠ (1, 0) →
    stageRow ell x = stageRow (ell + d) y →
    N d < sourceSize x

def CrossStageBudgetOpen (k ell d : ℕ) : Prop :=
  CrossStageSourceExclusion ell k d ∧
    ∃ (a b τ : ℤ),
      0 ≤ τ ∧
      conePoint (Nat.fib (3 * k - 1) : ℤ) (Nat.fib (3 * k) : ℤ)
        (fibrePoint ell a b (-τ))

end D5.S3.Arith.FibonacciAtomic.CrossStageCollisionBudget

#print axioms D5.S3.Arith.FibonacciAtomic.CrossStageCollisionBudget.CrossStageSourceExclusionAndEndpointMinimization
