/- GID: D5/S0/Conventions/IntegerIndexBinomial
   generality: G
   mirror-B: D5/B/S0/Conventions/IntegerIndexBinomial
   mirror-E: none(waiver:notation-only)
   anchors: []
   utility: none
   digest: The binomial coefficient with a natural upper index and an integer lower index, zero when the lower index is negative. -/

import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Conventions.IntegerIndexBinomial

/-- `binom m j` is the binomial coefficient `C(m, j)` for a natural upper index `m` and an integer
lower index `j`: zero for `j < 0`, and `Nat.choose m j` otherwise (so also zero for `j > m`). -/
def binom (m : Nat) (j : Int) : Int :=
  if j < 0 then 0 else (Nat.choose m j.toNat : Int)

end D5.S0.Conventions.IntegerIndexBinomial
