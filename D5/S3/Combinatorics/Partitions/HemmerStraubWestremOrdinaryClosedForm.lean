/- GID: D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinaryClosedForm
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinaryClosedForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full ordinary-character HSW averages consume the weighted coefficient evaluation. -/

import D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinary
import D5.S3.Combinatorics.Partitions.HemmerStraubWestremWeightedAverage

/-!
The second import is the canonical coefficient owner published in PR 23734,
revision 69f68474a0566d6f465a14259b74f28b58e293f3. It is an external source
prerequisite of this composition. Its implementation is not copied here.
The binomial evaluation is used through its existing result and exact rational
operands. The ordinary operands remain the independently defined complex traces.
Escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/

namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinaryClosedForm

open D5.S3.Combinatorics.Partitions

/-- Both original ordinary-character averages, with every original quantifier and
the common parity-dependent value. The rectangle is present also when n is odd. -/
theorem result (n : ℕ) (hn : 1 ≤ n) :
    HemmerStraubWestremOrdinary.leftAverage n = HemmerStraubWestremOrdinary.rightAverage n ∧
      HemmerStraubWestremOrdinary.leftAverage n =
        (if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℂ) else 0) ∧
      HemmerStraubWestremOrdinary.rightAverage n =
        (if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℂ) else 0) := by
  have transport := HemmerStraubWestremOrdinary.averages_eq_frobenius n
  change
    HemmerStraubWestremOrdinary.leftAverage n =
        (HemmerStraubWestremWeightedAverage.leftAverage n : ℂ) ∧
      HemmerStraubWestremOrdinary.rightAverage n =
        (HemmerStraubWestremWeightedAverage.rightAverage n : ℂ) at transport
  have coefficient := HemmerStraubWestremWeightedAverage.result n hn
  have equal := congrArg (fun q : ℚ => (q : ℂ)) coefficient.1
  have value : (HemmerStraubWestremWeightedAverage.rightAverage n : ℂ) =
      if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℂ) else 0 := by
    have h := congrArg (fun q : ℚ => (q : ℂ)) coefficient.2
    split_ifs with he
    · simpa only [if_pos he, Rat.cast_natCast] using h
    · simpa only [if_neg he, Rat.cast_zero] using h
  exact ⟨HemmerStraubWestremOrdinary.weighted_identity n hn,
    transport.1.trans (equal.trans value), transport.2.trans value⟩

end D5.S3.Combinatorics.Partitions.HemmerStraubWestremOrdinaryClosedForm
