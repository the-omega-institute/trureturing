/- GID: D5/S3/Analytic/GoldenTomography/CountdownMemoryNoiseLowerBound
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/CountdownMemoryNoiseLowerBound
   mirror-E: none(waiver:unbounded-renewal-and-noise-lower-bound)
   anchors: []
   utility: none
   digest: A nilpotent countdown hides weak memory taps at every noisy observation time. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Analytic.GoldenTomography.CountdownMemoryNoiseLowerBound

private def hiddenStep (J : Nat) (theta : Real) (x : Nat → Real) (i : Nat) : Real :=
  if i < J then if i = 0 then 0 else theta * x (i-1) else 0

private def hiddenOrbit (J : Nat) (theta : Real) : Nat → Nat → Real
  | 0, i => if i = 0 ∧ i < J then 1 else 0
  | n+1, i => hiddenStep J theta (hiddenOrbit J theta n) i

private theorem hiddenOrbit_eq (J : Nat) (theta : Real) (n i : Nat) :
    hiddenOrbit J theta n i = if i = n ∧ i < J then theta^n else 0 := by
  induction n generalizing i with
  | zero => simp [hiddenOrbit]
  | succ n ih =>
      change hiddenStep J theta (hiddenOrbit J theta n) i = _
      by_cases hi : i < J
      · by_cases hz : i = 0
        · subst i
          simp [hiddenStep]
        · rw [hiddenStep, if_pos hi, if_neg hz, ih]
          by_cases he : i-1 = n
          · have hei : i = n+1 := by omega
            subst i
            have hn : n < J := by omega
            simp [hi, hn, pow_succ, mul_comm]
          · have hei : i ≠ n+1 := by omega
            simp [he, hei]
      · simp [hiddenStep, hi]

/-- Output of an actual finite nilpotent shift orbit. The readout weight at i
is delta/theta^i. This definition does not assume a spectral decomposition. -/
noncomputable def countdownMemory (J : Nat) (delta theta : Real) (n : Nat) : Real :=
  ∑ i ∈ Finset.range J, (delta / theta^i) * hiddenOrbit J theta n i

/-- A J-state shift with all eigenvalues zero has J nonzero target taps.
No distinct-eigenvalue or lower-coupling assumption occurs. -/
theorem countdown_memory_eq (J : Nat) (delta theta : Real) (ht : theta ≠ 0)
    (n : Nat) : countdownMemory J delta theta n = if n < J then delta else 0 := by
  unfold countdownMemory
  simp_rw [hiddenOrbit_eq]
  by_cases hn : n < J
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp only [true_and, if_pos hn]
      exact div_mul_cancel₀ delta (pow_ne_zero n ht)
    · intro i _ hin
      simp [hin]
    · intro hmem
      exact (hmem (Finset.mem_range.mpr hn)).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i ≠ n := by
      intro he
      subst i
      exact hn (Finset.mem_range.mp hi)
    simp [hin]

/-- Renewal response for first-return masses delta at times 2,...,J+1.
The direct term accounts for return with no intervening renewal. The sum
accounts for strictly earlier positive-time renewals. -/
noncomputable def renewalResponse (J : Nat) (delta : Real) : Nat → Real
  | 0 => 1
  | n+1 =>
      (if 2 ≤ n+1 ∧ n+1 ≤ J+1 then delta else 0) +
      delta * ∑ i ∈ Finset.range J,
        if i+2 < n+1 then renewalResponse J delta ((n+1)-(i+2)) else 0
termination_by n => n
decreasing_by omega

private theorem renewal_range (J : Nat) (delta : Real) (hd : 0 ≤ delta)
    (hm : (J : Real) * delta ≤ 1 / 2) (n : Nat) :
    0 ≤ renewalResponse J delta n ∧
      (n ≠ 0 → renewalResponse J delta n ≤ 2*delta) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [renewalResponse]
      | succ n =>
          have hterm (i : Nat) :
              0 ≤ (if i+2 < n+1 then
                renewalResponse J delta ((n+1)-(i+2)) else 0) := by
            split_ifs with h
            · exact (ih _ (by omega)).1
            · exact le_rfl
          have hterm_upper (i : Nat) :
              (if i+2 < n+1 then
                renewalResponse J delta ((n+1)-(i+2)) else 0) ≤ 2*delta := by
            split_ifs with h
            · exact (ih _ (by omega)).2 (by omega)
            · positivity
          have hsum : (∑ i ∈ Finset.range J,
              if i+2 < n+1 then renewalResponse J delta ((n+1)-(i+2)) else 0)
                ≤ (J : Real)*(2*delta) := by
            calc
              _ ≤ ∑ _i ∈ Finset.range J, (2*delta) :=
                Finset.sum_le_sum (fun i _ => hterm_upper i)
              _ = _ := by simp [mul_comm]
          have hsource0 :
              0 ≤ (if 2 ≤ n+1 ∧ n+1 ≤ J+1 then delta else 0) := by
            split_ifs <;> positivity
          have hsource1 :
              (if 2 ≤ n+1 ∧ n+1 ≤ J+1 then delta else 0) ≤ delta := by
            split_ifs <;> linarith
          have hsmall : delta + delta*((J : Real)*(2*delta)) ≤ 2*delta := by
            have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*delta by positivity)
            nlinarith
          constructor
          · rw [renewalResponse]
            exact add_nonneg hsource0
              (mul_nonneg hd (Finset.sum_nonneg (fun i _ => hterm i)))
          · intro _
            rw [renewalResponse]
            exact le_trans (add_le_add hsource1
              (mul_le_mul_of_nonneg_left hsum hd)) hsmall

/-- Response of the killed visible state with no possible return. -/
noncomputable def noReturnResponse (n : Nat) : Real := if n = 0 then 1 else 0

/-- Target loss on the first J memory coefficients, hence a lower bound on
any full-sequence absolute loss whenever that loss is defined. -/
noncomputable def prefixLoss (J : Nat) (f m : Nat → Real) : Real :=
  ∑ j ∈ Finset.range J, |f j - m j|

/-- One observation sequence is within delta of both true responses at EVERY
natural time. Every possible estimate from that same data incurs loss at least
J*delta/2 on one of the two actual memory targets. The statement quantifies over
arbitrary J and all estimates; it is not a finite numerical counterexample. -/
theorem countdown_noise_lower_bound (J : Nat) (delta theta : Real)
    (hd : 0 ≤ delta) (ht : theta ≠ 0) (hm : (J : Real) * delta ≤ 1 / 2) :
    ∃ y : Nat → Real,
      (∀ n : Nat,
        |y n - noReturnResponse n| ≤ delta ∧
        |y n - renewalResponse J delta n| ≤ delta) ∧
      (∀ f : Nat → Real,
        (J : Real)*delta/2 ≤
          max (prefixLoss J f (fun _ => 0))
            (prefixLoss J f (countdownMemory J delta theta))) := by
  let y : Nat → Real := fun n =>
    (renewalResponse J delta n + noReturnResponse n)/2
  refine ⟨y, ?_, ?_⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      simp [y, noReturnResponse, renewalResponse, hd]
    · have hr := renewal_range J delta hd hm n
      have hu := hr.2 hn
      have hz : noReturnResponse n = 0 := by simp [noReturnResponse, hn]
      constructor
      · apply abs_le.mpr
        dsimp [y]
        rw [hz]
        constructor <;> linarith [hr.1]
      · apply abs_le.mpr
        dsimp [y]
        rw [hz]
        constructor <;> linarith [hr.1]
  · intro f
    have hpoint (j : Nat) (hj : j ∈ Finset.range J) :
        delta ≤ |f j - (0 : Real)| + |f j - countdownMemory J delta theta j| := by
      rw [countdown_memory_eq J delta theta ht, if_pos (Finset.mem_range.mp hj)]
      have h1 := le_abs_self (f j)
      have h2 := le_abs_self (delta - f j)
      rw [abs_sub_comm delta (f j)] at h2
      simp only [sub_zero]
      linarith
    have hsep : (J : Real)*delta ≤
        prefixLoss J f (fun _ => 0) + prefixLoss J f (countdownMemory J delta theta) := by
      have hh := Finset.sum_le_sum hpoint
      simpa [prefixLoss, Finset.sum_add_distrib, mul_comm] using hh
    have h0 := le_max_left (prefixLoss J f (fun _ => 0))
      (prefixLoss J f (countdownMemory J delta theta))
    have h1 := le_max_right (prefixLoss J f (fun _ => 0))
      (prefixLoss J f (countdownMemory J delta theta))
    linarith

#print axioms countdown_memory_eq
#print axioms countdown_noise_lower_bound

end D5.S3.Analytic.GoldenTomography.CountdownMemoryNoiseLowerBound
