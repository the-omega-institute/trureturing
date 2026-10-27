/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedCollisionSlice
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedCollisionSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact intermediate modes and supported inverse of a fixed collision slice. -/

import D5.S3.VertexAlgebra.FormalSeries.SupportedChannelSeries
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Lattice.Fold

/-!
This is a coefficient slice of the actual fixed clearing polynomial, before
the remaining s=x+y expansion. It does not assert finiteness for that later
expansion. The supported binomial inverse is reused, with the Carnahan
attribution retained in SupportedChannelSeries.

For signed b, the coefficient of y^b in
 s^k(s-y)^k y^k (y+z)^A z^B F(s,y,z)
uses F at y-exponent b-k-p-h, 0<=p<=k, 0<=h<=A.
The associated mode is -b+k+p+h-1. We prove both directions of its exact
integer interval description. An auxiliary s cutoff is subsequently used
only to invert (s+z)^C; it changes neither this fiber nor k,A,B.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.SupportedCollisionSlice
open SupportedChannelSeries
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section

/-- Mode indices, not exponents. The signed target b is unrestricted. -/
def modeFiber (k A : ℕ) (b : ℤ) : Finset ℤ :=
  Finset.Icc (-b + k - 1) (-b + 2 * k + A - 1)

/-- Exact index relevance in the displayed polynomial slice. This describes
indices of terms; zero states may of course shrink their nonzero support. -/
theorem mem_modeFiber_iff (k A : ℕ) (b r : ℤ) :
    r ∈ modeFiber k A b ↔
      ∃ p : ℕ, p ≤ k ∧ ∃ h : ℕ, h ≤ A ∧
        r = -b + k + p + h - 1 := by
  classical
  rw [modeFiber, Finset.mem_Icc]
  constructor
  · rintro ⟨lo, hi⟩
    let d : ℕ := (r + b - k + 1).toNat
    have hd : (d : ℤ) = r + b - k + 1 := by
      dsimp only [d]
      omega
    have bound : d ≤ k + A := by omega
    by_cases small : d ≤ k
    · exact ⟨d, small, 0, Nat.zero_le _, by omega⟩
    · exact ⟨k, le_rfl, d - k, by omega, by omega⟩
  · rintro ⟨p, hp, h, hh, rfl⟩
    constructor <;> omega


end
end D5.S3.VertexAlgebra.SupportedCollisionSlice
