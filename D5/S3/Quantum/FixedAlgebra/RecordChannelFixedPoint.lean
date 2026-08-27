/- GID: D5/S3/Quantum/FixedAlgebra/RecordChannelFixedPoint
   generality: G
   mirror-B: D5/B/S3/Quantum/FixedAlgebra/RecordChannelFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Record-channel fixed points are characterized entrywise by the Gram factors. -/

import D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality

/- Library-search audit trail (2026-08-27):
   * Exact repository body-shape hits `SingletonRecordClassicality.recordGram` and
     `SingletonRecordClassicality.recordChannel` are imported and used directly.
   * Existing fixed-point results are qubit-specific or require normalized,
     pairwise-distinct records; no exact theorem states the unrestricted entrywise
     product equation for arbitrary finite dimensions.
   * Pinned Mathlib search for a record-channel fixed-point characterization found
     no exact declaration; `Matrix.ext` and ring normalization prove the bridge.
   * No new `def` or `abbrev` is introduced, so there is no definitional fork.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.FixedAlgebra.RecordChannelFixedPoint

open D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality

/-- Entrywise comparison of the canonical record channel is exactly the
fixed-point equation `(G_ij - 1) * rho_ij = 0`. -/
theorem record_channel_fixed_iff_entry_equations
    {d e : Nat}
    (record : Fin d → Fin e → ℂ)
    (rho : Matrix (Fin d) (Fin d) ℂ) :
    recordChannel record rho = rho ↔
      ∀ i j, (recordGram record i j - 1) * rho i j = 0 := by
  constructor
  · intro hFixed i j
    have hEntry := congrArg (fun matrix : Matrix (Fin d) (Fin d) ℂ => matrix i j) hFixed
    change (recordGram record i j - 1) * rho i j = 0
    calc
      (recordGram record i j - 1) * rho i j =
          recordGram record i j * rho i j - rho i j := by ring
      _ = 0 := sub_eq_zero.mpr hEntry
  · intro hEntries
    ext i j
    change recordGram record i j * rho i j = rho i j
    calc
      recordGram record i j * rho i j =
          (recordGram record i j - 1) * rho i j + rho i j := by ring
      _ = 0 + rho i j := by rw [hEntries i j]
      _ = rho i j := zero_add _

#print axioms record_channel_fixed_iff_entry_equations

end D5.S3.Quantum.FixedAlgebra.RecordChannelFixedPoint
