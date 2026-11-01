/- GID: D5/S0/Conventions/BallotCoefficient
   generality: G
   mirror-B: D5/B/S0/Conventions/BallotCoefficient
   mirror-E: none(waiver:notation-only)
   anchors: []
   utility: none
   digest: Ballot coefficients as differences of binomial coefficients with integer lower indices. -/

import D5.S0.Conventions.IntegerIndexBinomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Conventions.BallotCoefficient

open D5.S0.Conventions.IntegerIndexBinomial (binom)

/-- The ballot coefficient, with negative lower binomial indices interpreted as zero. -/
def ballotE (r b : Nat) : Int :=
  binom (r + b - 1) ((b : Int) - 1) - binom (r + b - 1) ((b : Int) - 2)

end D5.S0.Conventions.BallotCoefficient
