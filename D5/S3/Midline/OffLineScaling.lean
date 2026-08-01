/- GID: D5/S3/Midline/OffLineScaling
   generality: I
   mirror-B: D5/B/S3/Midline/OffLineScaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Off-line nonempty ledger entries share a sign and grow unbounded under scaling. -/

import D5.S3.Zeros.ZeroGeometry

namespace D5.S3.Midline.OffLineScaling

open D5.S3.Weil.Convention D5.S3.Weil.LabeledZeta
open D5.S3.Weil.ReflectionLedger D5.S3.Zeros.ZeroGeometry

/-- Away from the critical line, every positive-length ledger entry is nonzero, all such
entries have the same sign, and every positive-length address has an unbounded sequence of
natural multiples. This is a coordinatewise fact only, not a claim about the sum after
analytic continuation, where cancellation is treated separately. -/
theorem off_line_scaling_ledger_growth {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (s : ℂ) (hOff : s.re ≠ criticalAbscissa) :
    (∀ a, 0 < length a → scalingLedger length s a ≠ 0) ∧
      (∀ a b, 0 < length a → 0 < length b →
        (0 < scalingLedger length s a ↔ 0 < scalingLedger length s b)) ∧
      (∀ (a : A) (m : ℕ),
        scalingLedger length s (m • a) = m * scalingLedger length s a) ∧
      (∀ a, 0 < length a → ∀ C : ℝ, ∃ m : ℕ,
        C < |scalingLedger length s (m • a)|) := by
  constructor
  · intro a ha
    exact ((off_line_scaling_entry_spec length s a ha).2.1).2 hOff
  constructor
  · intro a b ha hb
    exact (off_line_scaling_entry_spec length s a ha).2.2.1.trans
      (off_line_scaling_entry_spec length s b hb).2.2.1.symm
  constructor
  · intro a m
    simp [scalingLedger, map_nsmul]
    ring
  · intro a ha C
    have hEntry : scalingLedger length s a ≠ 0 :=
      ((off_line_scaling_entry_spec length s a ha).2.1).2 hOff
    have hAbs : 0 < |scalingLedger length s a| := abs_pos.mpr hEntry
    obtain ⟨m, hm⟩ := exists_nat_gt (C / |scalingLedger length s a|)
    refine ⟨m, ?_⟩
    rw [show scalingLedger length s (m • a) = m * scalingLedger length s a by
      simp [scalingLedger, map_nsmul]
      ring]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
    exact (div_lt_iff₀ hAbs).mp hm

end D5.S3.Midline.OffLineScaling
