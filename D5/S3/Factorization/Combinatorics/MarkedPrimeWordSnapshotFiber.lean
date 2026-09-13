/- GID: D5/S3/Factorization/Combinatorics/MarkedPrimeWordSnapshotFiber
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/MarkedPrimeWordSnapshotFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked prime words split uniquely into the prime words of successive divisor quotients. -/

import D5.S3.Factorization.Combinatorics.PrimeGenealogyCount
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.OfFn
import Mathlib.Order.Fin.Basic

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.MarkedPrimeWordSnapshotFiber

/-- A prime word is an ordered list of prime labels whose actual product is the endpoint. -/
def PrimeWord (n : ℕ) :=
  {w : List ℕ // (∀ p ∈ w, Nat.Prime p) ∧ w.prod = n}

/-- A snapshot records the actual prefix products at strictly increasing marks,
including the empty prefix and the complete prime word. -/
def SnapshotFiber (n k : ℕ) (d : Fin (k + 1) → ℕ) :=
  {z : PrimeWord n × (Fin (k + 1) → ℕ) //
    z.2 0 = 0 ∧ z.2 (Fin.last k) = z.1.val.length ∧ StrictMono z.2 ∧
    ∀ i : Fin (k + 1), (z.1.val.take (z.2 i)).prod = d i}

end D5.S3.Factorization.Combinatorics.MarkedPrimeWordSnapshotFiber
