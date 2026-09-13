/- GID: D5/S3/Observer/ProbabilisticClosure/DampedObservationRevival
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/DampedObservationRevival
   mirror-E: none(waiver:exact-damped-evolution)
   anchors: []
   utility: none
   digest: A strictly decaying two-mode state can have a zero initial readout
     followed by positive observations; dynamical decay and visibility differ. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Filter
open scoped Topology

namespace D5.S3.Observer.ProbabilisticClosure.DampedObservationRevival

/-- Actual autonomous evolution after an initial signed two-mode excitation.
There is no external input after time zero. -/
def residualEvolution (a b : Real) : Nat → Real × Real
  | 0 => (1, -1)
  | n + 1 =>
      let x := residualEvolution a b n
      (a * x.1, b * x.2)

/-- A scalar readout can cancel even when both state components are present. -/
def observed (a b : Real) (n : Nat) : Real :=
  (residualEvolution a b n).1 + (residualEvolution a b n).2

/-- Squared Euclidean amplitude, not a claimed physiological energy. -/
def amplitudeSquared (a b : Real) (n : Nat) : Real :=
  (residualEvolution a b n).1 ^ 2 + (residualEvolution a b n).2 ^ 2

/-- Exact response, strict decay of the underlying amplitude, revival of the
initially invisible readout, and its eventual vanishing hold simultaneously.
This is a mathematical distinction between attenuation and cancellation;
it does not formalize a claim about human cognition or a particular brain. -/
theorem decay_and_visibility_are_distinct {a b : Real}
    (hb : 0 < b) (hba : b < a) (ha : a < 1) :
    (∀ n : Nat, residualEvolution a b n = (a^n, -(b^n))) ∧
    observed a b 0 = 0 ∧
    (∀ n : Nat, 0 < n → 0 < observed a b n) ∧
    (∀ n : Nat, amplitudeSquared a b (n + 1) < amplitudeSquared a b n) ∧
    (∀ n : Nat, observed a b (n + 1) - observed a b n =
      (1-b)*b^n - (1-a)*a^n) ∧
    Tendsto (observed a b) atTop (𝓝 0) := by
  have ha0 : 0 < a := lt_trans hb hba
  have hb1 : b < 1 := lt_trans hba ha
  have hstate : ∀ n : Nat, residualEvolution a b n = (a^n, -(b^n)) := by
    intro n
    induction n with
    | zero => simp [residualEvolution]
    | succ n ih =>
      rw [residualEvolution, ih]
      apply Prod.ext <;> simp only [pow_succ] <;> ring
  have horder : ∀ n : Nat, b^(n+1) < a^(n+1) := by
    intro n
    induction n with
    | zero => simpa using hba
    | succ n ih =>
      calc
        b ^ (n + 1 + 1) = b ^ (n + 1) * b := pow_succ _ _
        _ < a ^ (n + 1) * b := mul_lt_mul_of_pos_right ih hb
        _ < a ^ (n + 1) * a := mul_lt_mul_of_pos_left hba (pow_pos ha0 (n+1))
        _ = a ^ (n + 1 + 1) := (pow_succ _ _).symm
  refine ⟨hstate, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [observed, residualEvolution]
  · intro n hn
    cases n with
    | zero => omega
    | succ k => simpa [observed, hstate] using sub_pos.mpr (horder k)
  · intro n
    have hda : 0 < 1-a^2 := by nlinarith
    have hdb : 0 < 1-b^2 := by nlinarith
    have hpa : 0 < (a^n)^2 := pow_pos (pow_pos ha0 n) 2
    have hpb : 0 < (b^n)^2 := pow_pos (pow_pos hb n) 2
    have hA := mul_pos hda hpa
    have hB := mul_pos hdb hpb
    simp only [amplitudeSquared, hstate, pow_succ, Prod.fst, Prod.snd]
    nlinarith
  · intro n
    simp only [observed, hstate, pow_succ, Prod.fst, Prod.snd]
    ring
  · have hA : Tendsto (fun n : Nat => a^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha
    have hB : Tendsto (fun n : Nat => b^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hb.le hb1
    simpa [observed, hstate, sub_eq_add_neg] using hA.sub hB

#print axioms decay_and_visibility_are_distinct

end D5.S3.Observer.ProbabilisticClosure.DampedObservationRevival
