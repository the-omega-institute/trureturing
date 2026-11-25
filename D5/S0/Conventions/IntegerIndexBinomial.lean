/- GID: D5/S0/Conventions/IntegerIndexBinomial
   generality: G
   mirror-B: D5/B/S0/Conventions/IntegerIndexBinomial
   mirror-E: none(waiver:notation-only)
   anchors: []
   utility: none
   digest: The binomial coefficient with a natural upper index and an integer lower index, zero when the lower index is negative. -/

import D5.S0.Conventions.IntegerIndexBinomial.Native
import OmegaMath.Data.Int
import OmegaMathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Conventions.IntegerIndexBinomial

/-- `binom m j` is the binomial coefficient `C(m, j)` for a natural upper index `m` and an integer
lower index `j`. Negative lower indices have coefficient zero. -/
noncomputable def binom (m : Omega.Nat) (j : Omega.Int) : Omega.Int :=
  Omega.Int.rec (fun k => Omega.Int.ofNat (OmegaMathlib.Nat.choose m k)) (fun _ => Omega.Int.zero) j

/-- The ballot coefficient, with negative lower binomial indices interpreted as zero. -/
noncomputable def ballotE (r b : Omega.Nat) : Omega.Int :=
  let upper := (r.add b).sub Omega.Nat.one
  let lower := Omega.Int.ofNat b
  (binom upper (lower.sub Omega.Int.one)).sub (binom upper (lower.sub Omega.Int.two))

end D5.S0.Conventions.IntegerIndexBinomial
