/- GID: D5/S3/Analytic/GoldenTomography/PronyTargetExtrapolation
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/PronyTargetExtrapolation
   mirror-E: none(waiver:unbounded-separation-free-error-bound)
   anchors: []
   utility: none
   digest: An initial moment block controls every later Prony target without separated nodes. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Analytic.GoldenTomography.PronyTargetExtrapolation

open FinitePronyHankelReconstruction

/-- A polynomial-in-time amplification factor at each fixed mode bound.
The empty sum is zero, so zero modes require no initial observations. -/
def amplification (d n : Nat) : Nat :=
  ∑ k ∈ Finset.range d, n.choose k * 2^k

private theorem amplification_zero (d : Nat) : amplification (d+1) 0 = 1 := by
  unfold amplification
  rw [Finset.sum_range_succ']
  simp

private theorem amplification_step (d n : Nat) :
    amplification (d+1) (n+1) = amplification (d+1) n + 2*amplification d n := by
  unfold amplification
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (f := fun k => n.choose k * 2^k) d]
  simp only [Nat.choose_zero_right, pow_zero, mul_one, Nat.choose_succ_succ,
    pow_succ, ← mul_assoc, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  ring

/-- Deflation removes one actual summand without division by any node gap. -/
private theorem deflation {d : Nat} (nodes weights : Fin (d+1) → Real) (n : Nat) :
    pronyMoment (fun j : Fin d => nodes j.succ)
      (fun j : Fin d => weights j.succ * (nodes j.succ - nodes 0)) n =
    pronyMoment nodes weights (n+1) - nodes 0 * pronyMoment nodes weights n := by
  calc
    _ = ∑ j : Fin (d+1), weights j * (nodes j - nodes 0) * nodes j^n := by
      rw [Fin.sum_univ_succ]
      simp [pronyMoment]
    _ = _ := by
      unfold pronyMoment
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring

/-- Signed weights, repeated nodes, and zero weights are all allowed.
The induction is on the actual finite mode family, not an assumed recurrence. -/
private theorem single_family_bound :
    ∀ d : Nat, ∀ nodes weights : Fin d → Real, ∀ epsilon : Real,
      0 ≤ epsilon → (∀ j, |nodes j| ≤ 1) →
      (∀ k : Nat, k < d → |pronyMoment nodes weights k| ≤ epsilon) →
      ∀ n : Nat, |pronyMoment nodes weights n| ≤ (amplification d n : Real)*epsilon := by
  intro d
  induction d with
  | zero =>
      intro nodes weights epsilon he hn hp n
      simp [pronyMoment, amplification]
  | succ d ih =>
      intro nodes weights epsilon he hn hp
      let ns : Fin d → Real := fun j => nodes j.succ
      let ws : Fin d → Real := fun j => weights j.succ * (nodes j.succ - nodes 0)
      have hdef (n : Nat) : pronyMoment ns ws n =
          pronyMoment nodes weights (n+1) - nodes 0 * pronyMoment nodes weights n :=
        deflation nodes weights n
      have hns (j : Fin d) : |ns j| ≤ 1 := hn j.succ
      have hprefix (k : Nat) (hk : k < d) : |pronyMoment ns ws k| ≤ 2*epsilon := by
        rw [hdef]
        calc
          _ ≤ |pronyMoment nodes weights (k+1)| +
              |nodes 0 * pronyMoment nodes weights k| := by
                simpa using (abs_sub_le (pronyMoment nodes weights (k+1)) 0
                  (nodes 0 * pronyMoment nodes weights k))
          _ = |pronyMoment nodes weights (k+1)| +
              |nodes 0| * |pronyMoment nodes weights k| := by rw [abs_mul]
          _ ≤ epsilon + 1*epsilon :=
            add_le_add (hp (k+1) (by omega))
              (mul_le_mul (hn 0) (hp k (by omega)) (abs_nonneg _) (by norm_num))
          _ = 2*epsilon := by ring
      have htail := ih ns ws (2*epsilon) (by positivity) hns hprefix
      intro n
      induction n with
      | zero =>
          rw [amplification_zero]
          simpa using hp 0 (by omega)
      | succ n ihn =>
          have hstep : pronyMoment nodes weights (n+1) =
              nodes 0 * pronyMoment nodes weights n + pronyMoment ns ws n := by
            rw [hdef]
            ring
          rw [hstep]
          calc
            _ ≤ |nodes 0 * pronyMoment nodes weights n| + |pronyMoment ns ws n| :=
              abs_add _ _
            _ = |nodes 0| * |pronyMoment nodes weights n| + |pronyMoment ns ws n| := by
              rw [abs_mul]
            _ ≤ 1*((amplification (d+1) n : Real)*epsilon) +
                (amplification d n : Real)*(2*epsilon) :=
              add_le_add (mul_le_mul (hn 0) ihn (abs_nonneg _) (by norm_num)) (htail n)
            _ = (amplification (d+1) (n+1) : Real)*epsilon := by
              rw [amplification_step]
              push_cast
              ring

/-- If two actual finite exponential families with nodes in [-1,1] agree to
error epsilon through degree d+e-1, their nth targets differ by at most
(sum_{k<d+e} binom(n,k) 2^k)*epsilon. There is no separation or nonzero-weight
hypothesis and no inversion of a Hankel matrix. For fixed d+e the factor is
polynomial in n; the theorem does not assert stable recovery of individual nodes. -/
theorem prony_target_error_bound
    {d e : Nat} (nodes weights : Fin d → Real) (otherNodes otherWeights : Fin e → Real)
    (epsilon : Real) (he : 0 ≤ epsilon)
    (hn : ∀ j, |nodes j| ≤ 1) (hm : ∀ j, |otherNodes j| ≤ 1)
    (hp : ∀ k : Nat, k < d+e →
      |pronyMoment nodes weights k - pronyMoment otherNodes otherWeights k| ≤ epsilon)
    (n : Nat) :
    |pronyMoment nodes weights n - pronyMoment otherNodes otherWeights n| ≤
      (amplification (d+e) n : Real)*epsilon := by
  let ns : Fin (d+e) → Real := Fin.addCases nodes otherNodes
  let ws : Fin (d+e) → Real := Fin.addCases weights (fun j => -otherWeights j)
  have hmoment (k : Nat) : pronyMoment ns ws k =
      pronyMoment nodes weights k - pronyMoment otherNodes otherWeights k := by
    simp [pronyMoment, ns, ws, Fin.sum_univ_add, sub_eq_add_neg,
      Finset.sum_neg_distrib]
  have hns : ∀ j, |ns j| ≤ 1 := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa [ns] using hn i
    · intro i
      simpa [ns] using hm i
  have hh : ∀ k : Nat, k < d+e → |pronyMoment ns ws k| ≤ epsilon := by
    intro k hk
    rw [hmoment]
    exact hp k hk
  have result := single_family_bound (d+e) ns ws epsilon he hns hh n
  simpa only [hmoment] using result

#print axioms prony_target_error_bound

end D5.S3.Analytic.GoldenTomography.PronyTargetExtrapolation
