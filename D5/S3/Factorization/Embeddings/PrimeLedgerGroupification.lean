/- GID: D5/S3/Factorization/Embeddings/PrimeLedgerGroupification
   generality: G
   mirror-B: D5/B/S3/Factorization/Embeddings/PrimeLedgerGroupification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Natural prime ledgers are forward-only; signed ledgers record explicit inverses. -/

import D5.S3.Factorization.PositiveRationalGroup

namespace D5.S3.Factorization.Embeddings.PrimeLedgerGroupification

open D5.S3.Factorization.PositiveRationalGroup

/-- Natural prime ledgers are exactly the nonnegative signed ledgers, while every signed
ledger is an explicit difference of a forward ledger and an inverse ledger. -/
theorem prime_ledger_direction_and_groupification (z : SignedPrimeLedger) :
    ((∃ forward : NaturalPrimeLedger, naturalLedgerCast forward = z) ↔
      ∀ p, 0 ≤ z p) ∧
    ∃ forward inverse : NaturalPrimeLedger,
      z = naturalLedgerCast forward - naturalLedgerCast inverse := by
  constructor
  · constructor
    · rintro ⟨forward, rfl⟩ p
      simp [naturalLedgerCast]
    · intro hz
      let forward : NaturalPrimeLedger :=
        z.mapRange Int.toNat Int.toNat_zero
      refine ⟨forward, ?_⟩
      ext p
      simpa [naturalLedgerCast, forward] using
        (Int.toNat_of_nonneg (hz p))
  · let forward : NaturalPrimeLedger :=
      z.mapRange Int.toNat Int.toNat_zero
    let inverse : NaturalPrimeLedger :=
      (-z).mapRange Int.toNat Int.toNat_zero
    refine ⟨forward, inverse, ?_⟩
    ext p
    change z p = ((z p).toNat : Int) - ((-z p).toNat : Int)
    exact (z p).toNat_sub_toNat_neg.symm

end D5.S3.Factorization.Embeddings.PrimeLedgerGroupification
