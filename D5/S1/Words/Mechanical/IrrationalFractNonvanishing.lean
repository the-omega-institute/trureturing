/- GID: D5/S1/Words/Mechanical/IrrationalFractNonvanishing
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Irrational reals have nonzero fractional part; every nonzero natural multiple of an irrational real has nonzero fractional part. -/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.NumberTheory.Real.Irrational

/- Provenance: Native proof over pinned mathlib. -/

/-!
SEARCH RECEIPT

Pinned-library reuse:
* `Mathlib/Algebra/Order/Floor/Ring.lean:457` provides
  `Int.fract_eq_zero_iff`, and `:460` provides its negated form
  `Int.fract_ne_zero_iff` used by both public proofs.
* `Mathlib/NumberTheory/Real/Irrational.lean:172` opens the `Irrational`
  namespace; `:183` provides `Irrational.ne_int`, used to contradict an
  integer representation of the argument; `:326` provides
  `Irrational.natCast_mul`, used for the nonzero natural multiple. The same
  file also contains the related equivalence
  `irrational_natCast_mul_iff` at `:494`, but it does not mention `Int.fract`.

Repository reuse and duplication audit:
* `D5/S1/Words/Mechanical/MechanicalFactorComplexity.lean:38-44` and
  `D5/S1/Words/Mechanical/MechanicalUniformRecurrence.lean:24-30` contain
  identical private proofs for the shifted factor `m + 1`.
* `D5/S1/Depth/GoldenContinuedFraction.lean:22-24` proves a golden-ratio
  special case by an explicit floor computation, and
  `D5/S1/Words/GoldenFactorComplexity.lean:49-55` inlines the same
  irrational-multiple argument.
* The same argument occurs in private declarations at
  `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.lean:25-30`,
  `D5/S1/Words/ReturnWords/GoldenRankArcs.lean:40-46`, and
  `D5/S1/Words/ReturnWords/GoldenReturnItinerary.lean:28-34`.
  These are instances, not reusable public declarations.

Negative findings:
* Repository search for public declarations named
  `irrational_fract_ne_zero`, `irrational_natCast_mul_fract_ne_zero`, or
  `fract_mul_alpha_ne_zero` found no result outside the private instances
  listed above.
* A broad pinned-library search for declarations combining `Irrational` with
  `Int.fract` found no direct theorem; the fractional-part family located was
  `Int.fract_eq_zero_iff`/`Int.fract_ne_zero_iff` above, while the other
  `fract_ne_zero` hits concern continued-fraction algorithm hypotheses rather
  than irrationality.

Conclusion on the frozen private copies:
* Because `private` declarations in the frozen modules are unreachable from
  other modules, publishing this conservative interface in a new file does
  not alter or expose those declarations and does not modify frozen files.
  The `m != 0` formulation is equivalent to their `m + 1` formulation by
  reindexing (`m + 1` is always nonzero), while also covering every nonzero
  natural multiplier directly; the hypothesis is therefore retained.
-/

namespace D5.S1.Words.Mechanical.IrrationalFractNonvanishing

/-- An irrational real cannot have zero fractional part. -/
theorem irrational_fract_ne_zero {x : Real} (hx : Irrational x) : Int.fract x ≠ 0 := by
  rw [Int.fract_ne_zero_iff]
  rintro ⟨z, hz⟩
  exact hx.ne_int z hz.symm

/-- A nonzero natural multiple of an irrational real cannot have zero fractional part. -/
theorem irrational_natCast_mul_fract_ne_zero {alpha : Real} (halpha : Irrational alpha)
    {m : Nat} (hm : m ≠ 0) : Int.fract ((m : Real) * alpha) ≠ 0 := by
  have hi : Irrational ((m : Real) * alpha) := halpha.natCast_mul hm
  exact irrational_fract_ne_zero hi

#print axioms irrational_fract_ne_zero
#print axioms irrational_natCast_mul_fract_ne_zero

end D5.S1.Words.Mechanical.IrrationalFractNonvanishing
