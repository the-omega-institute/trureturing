/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/TriangleSurplusPacking
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separate packed evaluations for the even and odd X coefficients of the triangle surplus. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleSurplusFormula
import Mathlib.NumberTheory.Zsqrtd.Basic

/-! Encode the shifted variables as `t` and `B^409`, using two integer components
with `t² = B`. The components pack the even and odd powers of the first
variable separately. -/

namespace RefinedBMV.Tracial.TriangleSurplus

/-- The packed digit mask, expressed as a geometric sum. -/
def fastMask (width digits : Nat) : Nat :=
  ((((1 : Nat) <<< (width * digits)) - 1) /
    (((1 : Nat) <<< width) - 1)) <<< (width - 1)

/-- An integer pair encodes the shifted X variable as the square root of the
radix and the shifted Y variable as the 409th power of the radix. -/
def packedSurplus (width : Nat) :
    Zsqrtd (↑((1 : Nat) <<< width) : ℤ) ×
      Zsqrtd (↑((1 : Nat) <<< width) : ℤ) × Zsqrtd (↑((1 : Nat) <<< width) : ℤ) :=
  surplus ⟨1, 1⟩ ⟨1 + ↑((1 : Nat) <<< (width * 409)), 0⟩

/-- Check one edge and one parity. The mask and powers remain parameterized so
the module does not contain a serialized large integer. -/
def packedCheck (width : Nat) (edgeIndex : Nat) (odd : Bool) : Bool :=
  let ps := packedSurplus width
  let s := if edgeIndex = 0 then ps.1 else if edgeIndex = 1 then ps.2.1 else ps.2.2
  let v := if odd then s.im else s.re
  let m := fastMask width (409 * 919)
  (((v + ↑m).toNat &&& m) == m) && (v != 0)

end RefinedBMV.Tracial.TriangleSurplus
