/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineMixedFactor
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cancel the shared double-single-single gap powers from the mixed Gram signs. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineSignPolynomials

/-! The three (R) coefficients each contain two of the same gap factors.
Removing them before forming the mixed signs keeps the certificate identity small. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

section Polynomial

variable {R : Type*} [Add R] [Sub R] [Mul R] [Neg R] [Pow R ℕ]
  [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4] [OfNat R 6]
  [OfNat R 11] [OfNat R 12] [OfNat R 14] [OfNat R 16]

def GramSign.sharedGapFactor (sign : GramSign) (q : Fin 12 → R) : R :=
  match sign with
  | .mixedFirst | .mixedLast => q 6 * q 7
  | .mixedMiddle => (q 6) ^ 2 * (q 7) ^ 2
  | _ => 1

def GramSign.valueWithoutSharedGaps (sign : GramSign) (q : Fin 12 → R) : R :=
  let s := q 6
  let t := q 7
  let w := q 8
  let A := 4 * q 0
  let B := 4 * q 2
  let C := 2 * q 9
  let D := 4 * q 1
  let E := 4 * q 4
  let F := 2 * q 10
  let G := 4 * q 3
  let L := 4 * q 5
  let K := 2 * q 11
  let d₁ := A * B - C ^ 2
  let d₂ := D * E - F ^ 2
  let d₃ := G * L - K ^ 2
  let α := w * A + t * D - (2 * s) ^ 2
  let β := w * B + s * G - (2 * t) ^ 2
  let J := A * G * E + D * B * L + 2 * C * F * K
  let RX := w * J + s * D * d₃ + t * G * d₂ -
    4 * (s ^ 2 * G * E + t ^ 2 * D * L + w ^ 2 * D * G
      + 2 * s * t * F * K - 2 * s * w * G * F - 2 * t * w * D * K)
  let RY := t * J + s * A * d₃ + w * L * d₁ -
    4 * (s ^ 2 * B * L + t ^ 2 * A * L + w ^ 2 * A * G
      - 2 * s * t * C * L + 2 * s * w * C * K - 2 * t * w * A * K)
  let RZ := s * J + t * B * d₂ + w * E * d₁ -
    4 * (s ^ 2 * B * E + t ^ 2 * A * E + w ^ 2 * B * D
      - 2 * s * t * C * E - 2 * s * w * B * F + 2 * t * w * C * F)
  match sign with
  | .mixedFirst => 2 * w * (D * RY + t * A * G * d₂) - α * RX
  | .mixedMiddle =>
    4 * w * (D * d₃ * RZ + G * d₂ * RY) - RX ^ 2 - 2 * α * β * d₂ * d₃
  | .mixedLast => 2 * w * (s * B * D * d₃ + G * RZ) - β * RX
  | _ => sign.value q

/-- The monomial and linear factors remaining after removing the shared gaps. -/
def GramSign.removedFactorWithoutSharedGaps (sign : GramSign) (x r t u v : R) : R :=
  let A := 1 - r
  let B := 1 - t
  let C := 1 - r * t
  match sign with
  | .mixedFirst => t^18 * v^4 * A^12 * B^11 * C^10 * (x+12) * (x+14)
  | .mixedMiddle => t^24 * v^4 * A^18 * B^14 * C^14 * (x+12)^2 * (x+14)^2
  | .mixedLast => t^18 * v^4 * A^12 * B^10 * C^11 * (x+12) * (x+14)
  | _ => sign.removedFactor x r t u v

end Polynomial

variable {R : Type*} [CommRing R]

theorem GramSign.factor_mul_removedFactorWithoutSharedGaps
    (sign : GramSign) (x r t u v : R) :
    sign.sharedGapFactor (affineEntries x r t u v) *
      sign.removedFactorWithoutSharedGaps x r t u v = sign.removedFactor x r t u v := by
  cases sign <;>
    simp only [sharedGapFactor, removedFactorWithoutSharedGaps, removedFactor, one_mul] <;>
    ac_rfl

set_option maxHeartbeats 0 in
-- Ring normalization checks the exact coefficient factorization.
theorem GramSign.factor_mul_valueWithoutSharedGaps (sign : GramSign) (q : Fin 12 → R) :
    sign.sharedGapFactor q * sign.valueWithoutSharedGaps q = sign.value q := by
  cases sign <;>
    simp only [sharedGapFactor, valueWithoutSharedGaps, value, one_mul,
      QuarticData.ofGapEntries, QuarticData.mixed1, QuarticData.mixed2, QuarticData.mixed3,
      QuarticData.RX, QuarticData.RY, QuarticData.RZ, QuarticData.J,
      QuarticData.KX, QuarticData.KY, QuarticData.KZ, QuarticData.delta1,
      QuarticData.delta2, QuarticData.delta3, QuarticData.alpha, QuarticData.beta] <;> ring

theorem GramSign.factor_mul_quotient_eq_of_reduced_identity
    (sign : GramSign) (x r t u v quotient : R)
    (h : sign.removedFactorWithoutSharedGaps x r t u v * quotient =
      sign.valueWithoutSharedGaps (affineEntries x r t u v)) :
    sign.removedFactor x r t u v * quotient = sign.value (affineEntries x r t u v) := by
  rw [← sign.factor_mul_removedFactorWithoutSharedGaps, mul_assoc, h,
    sign.factor_mul_valueWithoutSharedGaps]

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
