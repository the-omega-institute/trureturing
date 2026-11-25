/- GID: D5/S0/Conventions/IntegerIndexBinomial
   generality: G
   mirror-B: D5/B/S0/Conventions/IntegerIndexBinomial
   mirror-E: none(waiver:notation-only)
   anchors: []
   utility: none
   digest: The binomial coefficient with a natural upper index and an integer lower index, zero when the lower index is negative. -/

import Mathlib.Data.Nat.Choose.Basic
import OmegaMath.Data.Int
import OmegaMath.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Conventions.IntegerIndexBinomial

/-- `binom m j` is the binomial coefficient `C(m, j)` for a natural upper index `m` and an integer
lower index `j`. Negative lower indices have coefficient zero. -/
noncomputable def binom (m : Omega.Nat) (j : Omega.Int) : Omega.Int :=
  Omega.Int.rec (fun k => Omega.Int.ofNat (m.choose k)) (fun _ => Omega.Int.zero) j

/-- The ballot coefficient, with negative lower binomial indices interpreted as zero. -/
noncomputable def ballotE (r b : Omega.Nat) : Omega.Int :=
  let upper := (r.add b).sub Omega.Nat.one
  let lower := Omega.Int.ofNat b
  (binom upper (lower.sub Omega.Int.one)).sub (binom upper (lower.sub Omega.Int.two))

/-- The executable binomial coefficient in the standard natural and integer types. -/
def binom_std (m : Nat) (j : Int) : Int :=
  if j < 0 then 0 else (Nat.choose m j.toNat : Int)

/-- The executable ballot coefficient in the standard natural and integer types. -/
def ballotE_std (r b : Nat) : Int :=
  binom_std (r + b - 1) ((b : Int) - 1) - binom_std (r + b - 1) ((b : Int) - 2)

end D5.S0.Conventions.IntegerIndexBinomial
