/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteTraceChart
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteTraceChart
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCoordinates]
   utility: none
   digest: Affine trace-direction charts and physical shear of the five-site amplitude map. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCoordinates

/-! Shearing the physical basis lets the aligned source describe nonzero trace directions. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteTraceChart

open PeriodicMPSFiveSiteCoordinates

variable {R : Type*} [CommRing R]

/-- The fifth tensor power of the shear that replaces the second letter by
the second letter plus `s` times the first, on the eight necklace coordinates. -/
def shear (s : R) (p : Fin 8 → R) : Fin 8 → R :=
  ![p 0,
    p 1 + s * p 0,
    p 2 + 2 * s * p 1 + s ^ 2 * p 0,
    p 3 + 2 * s * p 1 + s ^ 2 * p 0,
    p 4 + s * (2 * p 2 + p 3) + 3 * s ^ 2 * p 1 + s ^ 3 * p 0,
    p 5 + s * (p 2 + 2 * p 3) + 3 * s ^ 2 * p 1 + s ^ 3 * p 0,
    p 6 + 2 * s * (p 4 + p 5) + 3 * s ^ 2 * (p 2 + p 3) + 4 * s ^ 3 * p 1 + s ^ 4 * p 0,
    p 7 + 5 * s * p 6 + 5 * s ^ 2 * (p 4 + p 5) + 5 * s ^ 3 * (p 2 + p 3) +
      5 * s ^ 4 * p 1 + s ^ 5 * p 0]

@[simp]
theorem shear_zero (p : Fin 8 → R) : shear 0 p = p := by
  funext i
  fin_cases i <;> simp [shear]

theorem shear_add (r s : R) (p : Fin 8 → R) : shear r (shear s p) = shear (r + s) p := by
  funext i
  fin_cases i <;> simp [shear] <;> ring

theorem shear_smul (s z : R) (p : Fin 8 → R) : shear s (z • p) = z • shear s p := by
  funext i
  fin_cases i <;> simp [shear, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The shear acts on the invariant trace tuple by the change of variables
in the binary determinant pencil. -/
theorem shear_coordinates (s t u d e k : R) :
    shear s (coordinates t u d e k) =
      coordinates t (u + s * t) d (e + s * (t * u - k) + s ^ 2 * d)
        (k + s * (t ^ 2 - 2 * d)) := by
  funext i
  fin_cases i <;> simp [shear, coordinates] <;> ring

/-- The first trace-direction chart, expressed as an amplitude vector before
normalizing its projective mass. -/
def chart (s x y z w : R) : Fin 8 → R := shear s (aligned x y z w)

theorem chart_trace_coordinates (s t d e k : R) :
    t • chart s (3 * d - t ^ 2) (2 * d - t ^ 2) (-k) e =
      coordinates t (s * t) d (e - s * k + s ^ 2 * d) (k + s * (t ^ 2 - 2 * d)) := by
  rw [chart, ← shear_smul, ← aligned_trace, shear_coordinates]
  simp only [zero_add, mul_zero, zero_sub, sub_eq_add_neg, mul_neg]

/-- The trace direction is read from the two antisymmetric differences even
after applying the shear to an aligned exceptional direction. -/
theorem shear_incidence (s : R) (p : Fin 8 → R) :
    shear s p 4 - shear s p 5 = p 4 - p 5 + s * (shear s p 2 - shear s p 3) := by
  simp [shear]
  ring

theorem chart_incidence (s x y z w : R) :
    chart s x y z w 4 - chart s x y z w 5 =
      s * (chart s x y z w 2 - chart s x y z w 3) := by
  rw [chart, shear_incidence]
  simp [aligned]

/-- Homogeneous amplitudes in a trace frame `(l₀, l₁)`, after removing the
common trace scale. The three determinant-pencil coefficients are `d, m, e`. -/
def frame (l₀ l₁ a d m e : R) : Fin 8 → R :=
  let k := a * l₀ * l₁ - m
  ![a ^ 2 * l₀ ^ 5 - 5 * d * a * l₀ ^ 3 + 5 * d ^ 2 * l₀,
    (a * l₀ ^ 3 - 2 * d * l₀) * k + (d ^ 2 - d * a * l₀ ^ 2) * l₁,
    l₁ * (a * l₀ ^ 2 - d) * k - e * a * l₀ ^ 3 - d * a * l₁ ^ 2 * l₀ +
      3 * d * e * l₀,
    l₀ * k ^ 2 - d * l₁ * k - d * e * l₀,
    (a * l₁ ^ 2 - e) * k * l₀ - d * a * l₁ ^ 3 - l₁ * e * a * l₀ ^ 2 +
      3 * l₁ * d * e,
    l₁ * k ^ 2 - e * k * l₀ - d * e * l₁,
    (a * l₁ ^ 3 - 2 * l₁ * e) * k + e ^ 2 * l₀ - a * l₁ ^ 2 * e * l₀,
    a ^ 2 * l₁ ^ 5 - 5 * e * a * l₁ ^ 3 + 5 * e ^ 2 * l₁]

theorem frame_trace_coordinates (t l₀ l₁ d m e : R) :
    coordinates (t * l₀) (t * l₁) d e (t ^ 2 * l₀ * l₁ - m) =
      t • frame l₀ l₁ (t ^ 2) d m e := by
  funext i
  fin_cases i <;> simp [coordinates, frame, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The frame change multiplies all eight amplitudes by the same unit whenever
`g` is a unit. The identity also holds on the boundary `a = 0`. -/
theorem frame_change (g l₀ l₁ a d m e : R) :
    frame (g * l₀) (g * l₁) a d m e = g • frame l₀ l₁ (g ^ 2 * a) d m e := by
  funext i
  fin_cases i <;> simp [frame, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The first trace-direction presentation agrees with the global frame formula
for every value of the squared trace scale. -/
theorem frame_first_chart (s a d m e : R) :
    frame 1 s a d (m + 2 * s * d) (e + s * m + s ^ 2 * d) =
      chart s (3 * d - a) (2 * d - a) m e := by
  funext i
  fin_cases i <;> simp [frame, chart, shear, aligned] <;> ring

theorem frame_incidence (l₀ l₁ a d m e : R) :
    l₀ * (frame l₀ l₁ a d m e 4 - frame l₀ l₁ a d m e 5) =
      l₁ * (frame l₀ l₁ a d m e 2 - frame l₀ l₁ a d m e 3) := by
  simp [frame]
  ring

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteTraceChart
