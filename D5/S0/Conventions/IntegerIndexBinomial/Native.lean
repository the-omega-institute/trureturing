/- GID: D5/S0/Conventions/IntegerIndexBinomial/Native
   generality: G
   mirror-B: D5/B/S0/Conventions/IntegerIndexBinomial/Native
   mirror-E: none(waiver:notation-only)
   anchors: []
   utility: none
   digest: Executable binomial and ballot coefficients with integer lower indices. -/

module

public import Mathlib.Data.Nat.Choose.Basic

/-! Binomial and ballot coefficients with integer lower indices. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Conventions.IntegerIndexBinomial

/-- The executable binomial coefficient in the standard natural and integer types. -/
def binom_std (m : Nat) (j : Int) : Int :=
  if j < 0 then 0 else (Nat.choose m j.toNat : Int)

/-- The executable ballot coefficient in the standard natural and integer types. -/
def ballotE_std (r b : Nat) : Int :=
  binom_std (r + b - 1) ((b : Int) - 1) - binom_std (r + b - 1) ((b : Int) - 2)

end D5.S0.Conventions.IntegerIndexBinomial
