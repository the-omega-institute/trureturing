/- GID: D5/S1/Words/Patterns/ArrowFixedPoint/Predicates
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/ArrowFixedPoint/Predicates
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Literal fixed-point arrow occurrences and their extremal characterizations. -/

import D5.S1.Words.Patterns.ArrowFixedPoint.CycleWord

/-!
# Fixed-point arrow predicates

Labels are zero-based `Fin n` values.  Thus `x : Fin n` represents the
paper's label `x.val + 1`.  The relation `Before pi a b` compares the
positions of the two labels in the actual one-line permutation `pi`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ArrowFixedPoint

open Equiv Equiv.Perm

noncomputable section

/-- Label `a` occurs before label `b` in the one-line permutation `pi`. -/
def Before {n : ℕ} (pi : Equiv.Perm (Fin n)) (a b : Fin n) : Prop :=
  pi.symm a < pi.symm b

/-- A literal occurrence of Zhou--Yu's `(12; 3 → 3)` arrow pattern. -/
def AlphaOccurs {n : ℕ} (pi : Equiv.Perm (Fin n)) : Prop :=
  ∃ x1 x2 x3 : Fin n,
    x1 < x2 ∧ x2 < x3 ∧ Before pi x1 x2 ∧ theta.symm pi x3 = x3

/-- A literal occurrence of Zhou--Yu's `(23; 1 → 1)` arrow pattern. -/
def BetaOccurs {n : ℕ} (pi : Equiv.Perm (Fin n)) : Prop :=
  ∃ x1 x2 x3 : Fin n,
    x1 < x2 ∧ x2 < x3 ∧ Before pi x2 x3 ∧ theta.symm pi x1 = x1

/-- Avoiding alpha means that below every `theta.symm`-fixed label, increasing
labels occur in decreasing positional order. -/
theorem alpha_avoid_iff_below_decreasing {n : ℕ} (pi : Equiv.Perm (Fin n)) :
    ¬ AlphaOccurs pi ↔
      ∀ f : Fin n, theta.symm pi f = f →
        ∀ x1 x2 : Fin n, x1 < x2 → x2 < f → ¬ Before pi x1 x2 := by
  constructor
  · intro havoid f hfix x1 x2 h12 h2f hbefore
    exact havoid ⟨x1, x2, f, h12, h2f, hbefore, hfix⟩
  · intro hdecreasing ⟨x1, x2, x3, h12, h23, hbefore, hfix⟩
    exact hdecreasing x3 hfix x1 x2 h12 h23 hbefore

/-- If `M` is the largest fixed label of `theta.symm pi`, alpha avoidance is
decided entirely by the labels below `M`. -/
theorem alpha_avoid_iff_below_largest_fixed {n : ℕ} (pi : Equiv.Perm (Fin n))
    (M : Fin n) (hM : theta.symm pi M = M)
    (hmax : ∀ f : Fin n, theta.symm pi f = f → f ≤ M) :
    ¬ AlphaOccurs pi ↔
      ∀ x1 x2 : Fin n, x1 < x2 → x2 < M → ¬ Before pi x1 x2 := by
  rw [alpha_avoid_iff_below_decreasing]
  constructor
  · intro h
    exact h M hM
  · intro h f hfix x1 x2 h12 h2f
    exact h x1 x2 h12 (lt_of_lt_of_le h2f (hmax f hfix))

/-- Avoiding beta means that above every `theta.symm`-fixed label, increasing
labels occur in decreasing positional order. -/
theorem beta_avoid_iff_above_decreasing {n : ℕ} (pi : Equiv.Perm (Fin n)) :
    ¬ BetaOccurs pi ↔
      ∀ f : Fin n, theta.symm pi f = f →
        ∀ x2 x3 : Fin n, x2 < x3 → f < x2 → ¬ Before pi x2 x3 := by
  constructor
  · intro havoid f hfix x2 x3 h23 hf2 hbefore
    exact havoid ⟨f, x2, x3, hf2, h23, hbefore, hfix⟩
  · intro hdecreasing ⟨x1, x2, x3, h12, h23, hbefore, hfix⟩
    exact hdecreasing x1 hfix x2 x3 h23 h12 hbefore

/-- If `m` is the smallest fixed label of `theta.symm pi`, beta avoidance is
decided entirely by the labels above `m`. -/
theorem beta_avoid_iff_above_smallest_fixed {n : ℕ} (pi : Equiv.Perm (Fin n))
    (m : Fin n) (hm : theta.symm pi m = m)
    (hmin : ∀ f : Fin n, theta.symm pi f = f → m ≤ f) :
    ¬ BetaOccurs pi ↔
      ∀ x2 x3 : Fin n, x2 < x3 → m < x2 → ¬ Before pi x2 x3 := by
  rw [beta_avoid_iff_above_decreasing]
  constructor
  · intro h
    exact h m hm
  · intro h f hfix x2 x3 h23 hf2
    exact h x2 x3 h23 (lt_of_le_of_lt (hmin f hfix) hf2)

end

end D5.S1.Words.Patterns.ArrowFixedPoint
