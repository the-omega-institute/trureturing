/- GID: D5/S3/Observer/ProbabilisticClosure/FiniteHorizonMemoryStability
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/FiniteHorizonMemoryStability
   mirror-E: none(waiver:unbounded-noncommutative-error-bound)
   anchors: []
   utility: none
   digest: Causal reconstruction in a normed operator algebra has an explicit
     finite-horizon perturbation bound, retaining the order of compositions. -/

import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.FiniteHorizonMemoryStability

/-- The same triangular causal inversion, now in a normed operator algebra so
that finite-precision errors can be stated without choosing hidden coordinates. -/
noncomputable def reconstruct {E : Type*} [Ring E] (R : Nat → E) (n : Nat) : E :=
  R (n+2)-R 1*R (n+1)-
    ∑ i : Fin n, reconstruct R (n-1-i.val)*R (i.val+1)
termination_by n
decreasing_by
  have := i.isLt
  omega

/-- Responses through time H+2 determine memory through lag H continuously.
The exact response/kernel recursion is the one supplied by block elimination.
Unit norm assumptions are explicit; this theorem neither assumes nor concludes
stable recovery of a hidden realization. Finite noisy samples are sufficient. -/
theorem finite_horizon_error_bound
    {E : Type*} [NormedRing E]
    (R M Rhat : Nat → E) (H : Nat) (epsilon : Real) (he : 0 ≤ epsilon)
    (hrec : ∀ n : Nat, M n = R (n+2)-R 1*R (n+1)-
      ∑ i : Fin n, M (n-1-i.val)*R (i.val+1))
    (hR : ∀ t : Nat, 1 ≤ t → t ≤ H+2 → ‖R t‖ ≤ 1)
    (hRh : ∀ t : Nat, 1 ≤ t → t ≤ H+2 → ‖Rhat t‖ ≤ 1)
    (hM : ∀ j : Nat, j ≤ H → ‖M j‖ ≤ 1)
    (herr : ∀ t : Nat, 1 ≤ t → t ≤ H+2 → ‖Rhat t-R t‖ ≤ epsilon) :
    ∀ n : Nat, n ≤ H →
      ‖reconstruct Rhat n-M n‖ ≤ ((2:Real)^(n+2)-1)*epsilon := by
  have productError (a b c d : E) :
      ‖a*b-c*d‖ ≤ ‖a-c‖*‖b‖+‖c‖*‖b-d‖ := by
    have hid : a*b-c*d = (a-c)*b+c*(b-d) := by noncomm_ring
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  have geometric : ∀ n : Nat,
      (∑ i : Fin n, (2:Real)^(n-1-i.val)) = 2^n-1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        (∑ i : Fin (n+1), (2:Real)^(n+1-1-i.val)) =
            2^n+∑ i : Fin n, (2:Real)^(n-1-i.val) := by
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Fin.val_succ, Nat.add_sub_cancel, Nat.sub_zero]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          have := i.isLt
          omega
        _ = 2^(n+1)-1 := by rw [ih, pow_succ]; ring
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hprod : ‖Rhat 1*Rhat (n+1)-R 1*R (n+1)‖ ≤ 2*epsilon := by
      calc
        _ ≤ ‖Rhat 1-R 1‖*‖Rhat (n+1)‖+‖R 1‖*‖Rhat (n+1)-R (n+1)‖ :=
          productError _ _ _ _
        _ ≤ epsilon*1+1*epsilon :=
          add_le_add
            (mul_le_mul (herr 1 (by omega) (by omega))
              (hRh (n+1) (by omega) (by omega)) (norm_nonneg _) he)
            (mul_le_mul (hR 1 (by omega) (by omega))
              (herr (n+1) (by omega) (by omega)) (norm_nonneg _) (by norm_num))
        _ = 2*epsilon := by ring
    have hterm (i : Fin n) :
        ‖reconstruct Rhat (n-1-i.val)*Rhat (i.val+1)-M (n-1-i.val)*R (i.val+1)‖ ≤
          (((2:Real)^(n-1-i.val+2)-1)*epsilon)+epsilon := by
      have hi := i.isLt
      have hj : n-1-i.val < n := by omega
      have hnonneg : 0 ≤ ((2:Real)^(n-1-i.val+2)-1)*epsilon := by
        have hp : (1:Real) ≤ 2^(n-1-i.val+2) := one_le_pow₀ (by norm_num)
        exact mul_nonneg (sub_nonneg.mpr hp) he
      calc
        _ ≤ ‖reconstruct Rhat (n-1-i.val)-M (n-1-i.val)‖*‖Rhat (i.val+1)‖+
            ‖M (n-1-i.val)‖*‖Rhat (i.val+1)-R (i.val+1)‖ := productError _ _ _ _
        _ ≤ (((2:Real)^(n-1-i.val+2)-1)*epsilon)*1+1*epsilon :=
          add_le_add
            (mul_le_mul (ih _ hj (by omega)) (hRh _ (by omega) (by omega))
              (norm_nonneg _) hnonneg)
            (mul_le_mul (hM _ (by omega)) (herr _ (by omega) (by omega))
              (norm_nonneg _) (by norm_num))
        _ = _ := by ring
    have hid : reconstruct Rhat n-M n =
        ((Rhat (n+2)-R (n+2))-(Rhat 1*Rhat (n+1)-R 1*R (n+1)))-
        ∑ i : Fin n,
          (reconstruct Rhat (n-1-i.val)*Rhat (i.val+1)-M (n-1-i.val)*R (i.val+1)) := by
      rw [reconstruct, hrec n, Finset.sum_sub_distrib]
      abel
    rw [hid]
    calc
      _ ≤ ‖(Rhat (n+2)-R (n+2))-(Rhat 1*Rhat (n+1)-R 1*R (n+1))‖+
          ‖∑ i : Fin n,
            (reconstruct Rhat (n-1-i.val)*Rhat (i.val+1)-M (n-1-i.val)*R (i.val+1))‖ :=
        norm_sub_le _ _
      _ ≤ (epsilon+2*epsilon)+∑ i : Fin n,
          ((((2:Real)^(n-1-i.val+2)-1)*epsilon)+epsilon) := by
        apply add_le_add
        · exact (norm_sub_le _ _).trans
            (add_le_add (herr _ (by omega) (by omega)) hprod)
        · exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hterm i))
      _ = 3*epsilon+4*epsilon*(∑ i : Fin n, (2:Real)^(n-1-i.val)) := by
        rw [show epsilon+2*epsilon = 3*epsilon by ring, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_add]
        norm_num
        ring
      _ = ((2:Real)^(n+2)-1)*epsilon := by
        rw [geometric n, pow_add]
        norm_num
        ring

#print axioms finite_horizon_error_bound

end D5.S3.Observer.ProbabilisticClosure.FiniteHorizonMemoryStability
