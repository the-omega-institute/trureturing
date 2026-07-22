/- GID: D5/S3/Zeros/ScalingLedgerConsequences
   generality: G
   mirror-B: D5/B/S3/Zeros/ScalingLedgerConsequences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact factorization and rigidity laws for coordinatewise scaling ledgers. -/

import D5.S3.Weil.CriticalLine

namespace D5.S3.Zeros.ScalingLedgerConsequences

open D5.S3.Weil.Convention
open D5.S3.Weil.LabeledZeta
open D5.S3.Weil.ReflectionLedger

/-- A coefficient at `1/2 + delta + it` splits into half-density, unit-phase,
and real-scaling factors. -/
theorem half_density_phase_scaling_factorization {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (delta t : Real) (a : A) :
    labeledZeta length
        (((criticalAbscissa + delta : Real) : Complex) +
          Complex.I * (t : Complex)) a =
        Complex.exp (-(criticalAbscissa : Complex) * (length a : Complex)) *
        Complex.exp (-(Complex.I * (t : Complex)) * (length a : Complex)) *
        Complex.exp (-(delta : Complex) * (length a : Complex)) := by
  simp only [labeledZeta]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Off the critical line, the absolute scaling entries along natural multiples
of any positive-length address exceed every real bound. -/
theorem scaling_ledger_unbounded_on_multiples {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (s : Complex) (a : A) (ha : 0 < length a)
    (hs : s.re ≠ criticalAbscissa) (bound : Real) :
    ∃ multiplier : Nat,
      bound < |scalingLedger length s (multiplier • a)| := by
  have hEntry : scalingLedger length s a ≠ 0 := by
    exact mul_ne_zero (sub_ne_zero.mpr hs) (ne_of_gt ha)
  have hPositive : 0 < |scalingLedger length s a| := abs_pos.mpr hEntry
  have hMultiple (multiplier : Nat) :
      scalingLedger length s (multiplier • a) =
        (multiplier : Real) * scalingLedger length s a := by
    simp [scalingLedger]
    ring
  obtain ⟨multiplier, hMultiplier⟩ :=
    exists_nat_gt (bound / |scalingLedger length s a|)
  refine ⟨multiplier, ?_⟩
  calc
    bound = (bound / |scalingLedger length s a|) *
        |scalingLedger length s a| := by
      field_simp [ne_of_gt hPositive]
    _ < (multiplier : Real) * |scalingLedger length s a| :=
      mul_lt_mul_of_pos_right hMultiplier hPositive
    _ = |scalingLedger length s (multiplier • a)| := by
      rw [hMultiple, abs_mul]
      simp

/-- Multiplication by a unit-modulus phase preserves every labeled
coefficient norm. -/
theorem unit_rotation_preserves_coefficient_norm {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (s rotation : Complex) (a : A)
    (hRotation : ‖rotation‖ = 1) :
    ‖rotation * labeledZeta length s a‖ = ‖labeledZeta length s a‖ := by
  rw [norm_mul, hRotation, one_mul]

end D5.S3.Zeros.ScalingLedgerConsequences
