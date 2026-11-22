/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteTraceChart
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteTraceChart
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCoordinates]
   utility: none
   digest: The periodic six-site trace graph is equivariant under physical shears. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCoordinates

/-! Physical basis shears and an adapted chart for the six-letter trace map. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteTraceChart

open PeriodicMPSSixSiteCoordinates

variable {R : Type*} [CommRing R]

/-- The change of the second physical letter by a multiple of the first,
acting multilinearly on the fourteen necklace coefficients. -/
def shear (s : R) (p : Fin 14 → R) : Fin 14 → R :=
  ![p 0,
    p 1 + s * p 0,
    p 2 + s * (2 * p 1) + s ^ 2 * p 0,
    p 3 + s * (2 * p 1) + s ^ 2 * p 0,
    p 4 + s * (2 * p 2 + p 3) + s ^ 2 * (3 * p 1) + s ^ 3 * p 0,
    p 5 + s * (2 * p 1) + s ^ 2 * p 0,
    p 6 + s * (p 2 + p 3 + p 5) + s ^ 2 * (3 * p 1) + s ^ 3 * p 0,
    p 7 + s * (p 2 + p 3 + p 5) + s ^ 2 * (3 * p 1) + s ^ 3 * p 0,
    p 8 + s * (2 * p 4 + p 6 + p 7) + s ^ 2 * (3 * p 2 + 2 * p 3 + p 5) + s ^ 3 * (4 * p 1) +
      s ^ 4 * p 0,
    p 9 + s * (3 * p 3) + s ^ 2 * (3 * p 1) + s ^ 3 * p 0,
    p 10 + s * (p 4 + p 6 + p 7 + p 9) + s ^ 2 * (2 * p 2 + 3 * p 3 + p 5) +
      s ^ 3 * (4 * p 1) + s ^ 4 * p 0,
    p 11 + s * (2 * p 6 + 2 * p 7) + s ^ 2 * (2 * p 2 + 2 * p 3 + 2 * p 5) +
      s ^ 3 * (4 * p 1) + s ^ 4 * p 0,
    p 12 + s * (2 * p 8 + 2 * p 10 + p 11) + s ^ 2 * (3 * p 4 + 3 * p 6 + 3 * p 7 + p 9) +
      s ^ 3 * (4 * p 2 + 4 * p 3 + 2 * p 5) + s ^ 4 * (5 * p 1) + s ^ 5 * p 0,
    p 13 + s * (6 * p 12) + s ^ 2 * (6 * p 8 + 6 * p 10 + 3 * p 11) +
      s ^ 3 * (6 * p 4 + 6 * p 6 + 6 * p 7 + 2 * p 9) + s ^ 4 * (6 * p 2 + 6 * p 3 + 3 * p 5) +
      s ^ 5 * (6 * p 1) + s ^ 6 * p 0]

@[simp]
theorem shear_zero (p : Fin 14 → R) : shear 0 p = p := by
  funext i
  fin_cases i <;> simp [shear]

theorem shear_add (r s : R) (p : Fin 14 → R) :
    shear r (shear s p) = shear (r + s) p := by
  funext i
  fin_cases i <;> simp [shear] <;> ring

theorem shear_smul (s a : R) (p : Fin 14 → R) : shear s (a • p) = a • shear s p := by
  funext i
  fin_cases i <;> simp [shear, Pi.smul_apply, smul_eq_mul] <;> ring

/-- A shear of a trace-aligned tuple translates the second trace and
transforms the determinant pencil by the same basis change. -/
theorem shear_aligned (s d e k : R) :
    shear s (coordinates 1 0 0 d e k) =
      coordinates 1 s (s ^ 2) d (e - s * k + s ^ 2 * d) (k + s * (1 - 2 * d)) := by
  funext i
  fin_cases i <;> simp [shear, coordinates] <;> ring

/-- The aligned amplitude depends linearly on the three normal coordinates
`(vacuum d, k, e)` after its higher-order terms are included in the matrix. -/
def lift (d e k : R) (z : Fin 3 → R) : Fin 14 → R :=
  ![z 0,
    (d ^ 2 - 3 * d + 1) * z 1,
    -(2 * d ^ 2 - 4 * d + 1) * z 2,
    (2 * d ^ 2 - d) * z 2 + (1 - d) * k * z 1,
    (d - 1) * e * z 1,
    -2 * d ^ 2 * z 2 + k * z 1,
    (d - 1) * e * z 1,
    (d - 1) * e * z 1,
    (1 - 2 * d) * e * z 2,
    (k ^ 2 - 3 * d * e) * z 1,
    (2 * d * e - k ^ 2) * z 2,
    (1 - 2 * d) * e * z 2,
    e ^ 2 * z 1,
    -2 * e ^ 2 * z 2]

theorem lift_smul (d e k a : R) (z : Fin 3 → R) :
    lift d e k (a • z) = a • lift d e k z := by
  funext i
  fin_cases i <;> simp [lift, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Factorization of the full trace chart including along paths tangent to a base conic. -/
theorem lift_coordinates (d e k : R) :
    lift d e k ![vacuum d, k, e] = coordinates 1 0 0 d e k := by
  funext i
  fin_cases i <;> simp [lift, coordinates, vacuum] <;> ring

/-- The projective normal directions have nonzero amplitude over each base conic. -/
theorem lift_ne_zero_of_vacuum {d : ℂ} (hd : vacuum d = 0)
    {z : Fin 3 → ℂ} (hz : z ≠ 0) : lift d 0 0 z ≠ 0 := by
  intro h
  apply hz
  have h₀ : z 0 = 0 := congrFun h 0
  have h₁ : (d ^ 2 - 3 * d + 1) * z 1 = 0 := congrFun h 1
  have h₂ : -(2 * d ^ 2 - 4 * d + 1) * z 2 = 0 := congrFun h 2
  obtain ⟨hK, hE⟩ := controlling_factors_ne hd
  have hz₁ := (mul_eq_zero.mp h₁).resolve_left hK
  have hz₂ := (mul_eq_zero.mp h₂).resolve_left (neg_ne_zero.mpr hE)
  funext i
  fin_cases i
  · exact h₀
  · exact hz₁
  · exact hz₂

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteTraceChart
