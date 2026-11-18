/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical chart changes and half-current lifts for the original four mixed inputs. -/

import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Real.Sqrt

/-! The physical order is P, Q, R, S at 1, z, 0, infinity. The elliptic
coordinate assigns 0, infinity, 1-r, 1 to the native order. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart

open Complex (I)
open HalfFock.OriginalHalfCurrentTransport

inductive Chart where
  | A | B | D

inductive Puncture where
  | P | Q | R | S

/-- The period arguments of the original A, B and D expressions. -/
def parameter : Chart → ℂ → ℂ
  | .A, z => 1 - z⁻¹
  | .B, z => z
  | .D, z => z⁻¹

private def p : Chart → ℂ → ℂ
  | .A, _ => 1
  | .B, z => z
  | .D, _ => 1

private def q : Chart → ℂ → ℂ
  | .A, z => z
  | .B, _ | .D, _ => 0

private def s : Chart → ℂ → ℂ
  | .A, _ => 0
  | .B, _ => 1
  | .D, z => z

private def d (c : Chart) (z : ℂ) : ℂ := 1 - parameter c z

/-- Physical coordinate at a finite point of the native elliptic chart. -/
def physical (c : Chart) (z x : ℂ) : ℂ :=
  (q c z * x - p c z) / (x - 1)

def pullB (z x : ℂ) : ℂ := (z - 1) / (z * x - 1)
def pullD (z x : ℂ) : ℂ := (z - 1)*x / (z * x - 1)

private theorem pullB_sub_one {z x : ℂ} (h : z * x - 1 ≠ 0) :
    pullB z x - 1 = -z*(x-1)/(z * x - 1) := by
  unfold pullB
  field_simp
  ring

private theorem pullD_sub_one {z x : ℂ} (h : z * x - 1 ≠ 0) :
    pullD z x - 1 = -(x-1)/(z * x - 1) := by
  unfold pullD
  field_simp
  ring

/-- Both transitions preserve the same physical point. The native right
puncture parameter is the cross ratio (s-p)/(s-q) in all three assignments. -/
theorem chart_changes {z x : ℂ} (hz : z ≠ 0)
    (hx : x ≠ 1) (h : z * x - 1 ≠ 0) :
    (∀ c, d c z = (s c z - p c z) / (s c z - q c z)) ∧
    physical .A z x = physical .B z (pullB z x) ∧
    physical .A z x = physical .D z (pullD z x) ∧
    pullB z x = 1 - (x-1)/(x-d .A z) ∧
    pullD z x = 1 - d .A z*(x-1)/(x-d .A z) := by
  have hx1 := sub_ne_zero.mpr hx
  have hd : x - d .A z = (z * x - 1)/z := by
    simp only [d, parameter, sub_sub_cancel]
    field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c
    cases c
    · simp [d, parameter, p, q, s, div_eq_mul_inv]
    · simp [d, parameter, p, q, s]
    · simp only [d, parameter, p, q, s, sub_zero]
      field_simp
  · simp only [physical, p, q, zero_mul, zero_sub, pullB_sub_one h]
    field_simp
  · simp only [physical, p, q, zero_mul, zero_sub, pullD_sub_one h]
    field_simp
  · rw [hd]
    unfold pullB
    field_simp
    ring
  · rw [hd]
    simp only [d, parameter, sub_sub_cancel, pullD]
    field_simp
    ring

private def leftP : Chart → Puncture
  | .A | .D => .P
  | .B => .Q

private def leftQ : Chart → Puncture
  | .A => .Q
  | .B | .D => .R

private def rightS : Chart → Puncture
  | .A => .R
  | .B => .P
  | .D => .Q

/-- The coordinate in the physical disk, centered separately at each
insertion, and using 1/Z at the detector. -/
def localCoordinate (c : Chart) (z : ℂ) (i : Puncture) (u : ℂ) : ℂ :=
  match c, i with
  | .A, .P | .D, .P => (p c z - q c z)*u/(1-u)
  | .A, .Q | .B, .R | .D, .R => (q c z - p c z)*u/(1-u)
  | .A, .R | .B, .P | .D, .Q => (q c z - s c z)*u
  | .B, .Q => (p c z - q c z)*u/(1-u)
  | _, .S => u/(q c z - s c z + s c z*u)

private def rightChart (d x : ℂ) : ℂ := (x-d)/(x-1)

private theorem physical_right {z u : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1) (hu : u ≠ 1) (c : Chart) :
    physical c z (rightChart (d c z) u) = s c z + (q c z - s c z) * u := by
  have hu' := sub_ne_zero.mpr hu
  have hd : 1 - d c z ≠ 0 := by
    rw [d, sub_sub_cancel]
    cases c
    · exact sub_ne_zero.mpr (fun h => hz1 (inv_eq_one.mp h.symm))
    · exact hz
    · exact inv_ne_zero hz
  have hright : rightChart (d c z) u - 1 = (1 - d c z)/(u-1) := by
    unfold rightChart
    field_simp
    ring
  have hp : p c z = s c z * (1 - d c z) + q c z * d c z := by
    cases c <;> simp [p, q, s, d, parameter, hz, mul_inv_cancel₀]
  rw [physical, hright, rightChart, hp]
  field_simp
  ring

/-- The local coordinates are the displacements induced by the same physical
map. The detector uses the reciprocal of that map. -/
theorem local_coordinates_from_physical {z u : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1)
    (hu : u ≠ 0) (hu1 : u ≠ 1) (c : Chart) :
    localCoordinate c z (leftP c) u = physical c z u - p c z ∧
    localCoordinate c z (leftQ c) u = physical c z u⁻¹ - q c z ∧
    localCoordinate c z (rightS c) u = physical c z (rightChart (d c z) u) - s c z ∧
    localCoordinate c z .S u = (physical c z (rightChart (d c z) u⁻¹))⁻¹ := by
  have hu' := sub_ne_zero.mpr hu1
  have hu'' : 1-u ≠ 0 := sub_ne_zero.mpr hu1.symm
  have hui : u⁻¹ ≠ 1 := by simpa using hu1
  have hui' := sub_ne_zero.mpr hui
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases c <;> simp only [localCoordinate, leftP, physical, p, q] <;>
      field_simp <;> ring
  · cases c <;> simp only [localCoordinate, leftQ, physical, p, q] <;>
      field_simp <;> ring
  · rw [physical_right hz hz1 hu1]
    cases c <;> simp [localCoordinate, rightS, q, s]
  · rw [physical_right hz hz1 hui, show s c z + (q c z - s c z) * u⁻¹ =
        (q c z - s c z + s c z*u) / u by field_simp; ring, inv_div]
    cases c <;> rfl

/-- Scale of the local coordinate in physical P,Q,R,S order. -/
def scale : Chart → ℂ → Puncture → ℂ
  | .A, z, .P => 1-z
  | .A, z, .Q => -(1-z)
  | .A, z, .R => z
  | .A, z, .S => z⁻¹
  | .B, _, .P | .B, _, .S | .D, _, .R => -1
  | .B, z, .Q => z
  | .B, z, .R | .D, z, .Q => -z
  | .D, _, .P => 1
  | .D, z, .S => -z⁻¹

/-- The three left pairs and the two reflected detector coordinates
all have the denominator 1-u. -/
def loweringParameter : Chart → Puncture → ℂ
  | .A, .R | .A, .S | .B, .P | .D, .Q => 0
  | _, _ => 1

theorem local_coordinate_derivatives (z : ℂ) (c : Chart) (i : Puncture) :
    (∀ u, localCoordinate c z i u =
      scale c z i * u / (1-loweringParameter c i*u)) ∧
    HasDerivAt (localCoordinate c z i) (scale c z i) 0 := by
  have formula : ∀ u, localCoordinate c z i u =
      scale c z i * u / (1-loweringParameter c i*u) := by
    intro u
    cases c <;> cases i <;>
      simp only [localCoordinate, scale, loweringParameter, p, q, s, zero_mul,
        sub_zero, one_mul, add_zero, zero_sub, div_eq_mul_inv, neg_mul] <;>
      try (ring_nf; done)
    · rw [show -1 + u = -(1-u) by ring, inv_neg]
      ring
    · rw [show -z + z * u = -(z * (1-u)) by ring, inv_neg, mul_inv]
      ring
  refine ⟨formula, ?_⟩
  rw [show localCoordinate c z i = fun u => scale c z i * u /
    (1-loweringParameter c i*u) from funext formula]
  simpa using (((hasDerivAt_id (0 : ℂ)).const_mul (scale c z i)).fun_div
    (((hasDerivAt_id (0 : ℂ)).const_mul (loweringParameter c i)).const_sub 1)
    (by simp : (1 - loweringParameter c i * id 0 : ℂ) ≠ 0))

private def rootZ (z : ℝ) : ℂ := Real.sqrt z
private def rootB (z : ℝ) : ℂ := Real.sqrt (1-z)

/-- The positive real scale takes the positive root and the negative scale
takes +i times the positive root of its absolute value. -/
def scaleRoot : Chart → ℝ → Puncture → ℂ
  | .A, z, .P => rootB z
  | .A, z, .Q => I * rootB z
  | .A, z, .R | .B, z, .Q => rootZ z
  | .A, z, .S => (rootZ z)⁻¹
  | .B, _, .P | .B, _, .S | .D, _, .R => I
  | .B, z, .R | .D, z, .Q => I * rootZ z
  | .D, _, .P => 1
  | .D, z, .S => I / rootZ z

/-- The root of 1-r on the specified lips. The D parameter approaches
the cut from below, so 1-r approaches the negative axis from above. -/
def periodRoot : Chart → ℝ → ℂ
  | .A, z => (rootZ z)⁻¹
  | .B, z => rootB z
  | .D, z => I * rootB z / rootZ z

private theorem rootZ_sq {z : ℝ} (hz : 0 < z) : rootZ z ^ 2 = (z : ℂ) := by
  unfold rootZ
  exact_mod_cast Real.sq_sqrt hz.le

private theorem rootB_sq {z : ℝ} (hz : z < 1) : rootB z ^ 2 = 1 - (z : ℂ) := by
  unfold rootB
  exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hz.le)

private theorem rootZ_ne {z : ℝ} (hz : 0 < z) : rootZ z ≠ 0 := by
  unfold rootZ
  exact_mod_cast (Real.sqrt_pos.2 hz).ne'

private theorem rootB_ne {z : ℝ} (hz : z < 1) : rootB z ≠ 0 := by
  unfold rootB
  exact_mod_cast (Real.sqrt_pos.2 (sub_pos.mpr hz)).ne'

private theorem scale_ne {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (c : Chart) (i : Puncture) :
    scale c z i ≠ 0 := by
  have h0 : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have h1 : (1 : ℂ) - z ≠ 0 := by exact_mod_cast (sub_pos.mpr hz1).ne'
  have h1' : (z : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp h1).symm
  cases c <;> cases i <;> simp [scale, h0, h1, h1']

theorem chosen_roots {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (c : Chart) (i : Puncture) :
    scaleRoot c z i ^ 2 = scale c z i ∧ periodRoot c z ^ 2 = d c z := by
  constructor
  · cases c <;> cases i <;>
      simp [scaleRoot, scale, mul_pow, inv_pow, rootZ_sq hz, rootB_sq hz1,
        Complex.I_sq, div_eq_mul_inv]
  · cases c <;>
      simp [periodRoot, d, parameter, mul_pow, div_pow, inv_pow,
        rootZ_sq hz, rootB_sq hz1, Complex.I_sq]
    have h0 : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    field_simp

private def rightSign : Chart → Puncture → ℂ
  | .A, .P | .A, .Q | .B, .Q | .B, .R | .D, .P | .D, .R => 1
  | _, _ => -1

private def outgoing : Chart → Puncture → Bool
  | .A, .Q | .B, .R | .D, .R | _, .S => true
  | _, _ => false

/-- This is signed m(0) divided by the root of the actual coordinate
derivative. The finite left and right raw coordinates have the same
inward branch normalization. -/
def halfDifferentialAt (c : Chart) (z : ℝ) (i : Puncture) : ℂ :=
  rightSign c i /
    ((if outgoing c i then 1 else periodRoot c z) * scaleRoot c z i)

def relativeB : Puncture → ℂ
  | .S => -1
  | _ => 1

def relativeD : Puncture → ℂ
  | .Q | .R => -1
  | _ => 1

/-- Relative signs of the four lifted sources on the real overlap. -/
theorem half_differential_signs {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (i : Puncture) :
    halfDifferentialAt .A z i =
      (-I * rootZ z) * relativeB i * halfDifferentialAt .B z i ∧
    halfDifferentialAt .A z i =
      I * relativeD i * halfDifferentialAt .D z i := by
  have hi := Complex.I_ne_zero
  have hI := Complex.I_sq
  have hs := rootZ_ne hz
  have ht := rootB_ne hz1
  cases i <;> constructor <;>
    simp only [halfDifferentialAt, rightSign, outgoing, periodRoot, scaleRoot, relativeB,
      relativeD, Bool.false_eq_true, ite_false, ite_true, one_mul] <;>
    field_simp
  simp [hI]

/-- The Legendre cubic in the native elliptic coordinate. -/
def cubic (c : Chart) (z x : ℂ) : ℂ := x*(x-1)*(x-d c z)

private def slopeB (z x : ℂ) : ℂ := z*(1-z)/(z * x - 1)^2
private def slopeD (z x : ℂ) : ℂ := (1-z)/(z * x - 1)^2

private theorem transition_slopes {z x : ℂ} (h : z * x - 1 ≠ 0) :
    HasDerivAt (pullB z) (slopeB z x) x ∧
    HasDerivAt (pullD z) (slopeD z x) x := by
  have hd := ((hasDerivAt_id x).const_mul z).sub_const 1
  constructor
  · refine ((hasDerivAt_const x (z-1)).fun_div hd h).congr_deriv ?_
    unfold slopeB
    simp only [zero_mul, zero_sub, mul_one, id_eq]
    ring
  · refine (((hasDerivAt_id x).const_mul (z-1)).fun_div hd h).congr_deriv ?_
    unfold slopeD
    simp only [mul_one, id_eq]
    ring

private theorem lifted_cubic {z x : ℂ} (hz : z ≠ 0) (h : z * x - 1 ≠ 0) :
    cubic .B z (pullB z x) = (-z) * slopeB z x ^ 2 * cubic .A z x ∧
    cubic .D z (pullD z x) = -slopeD z x ^ 2 * cubic .A z x := by
  constructor
  · unfold cubic slopeB
    rw [pullB_sub_one h]
    simp only [pullB, d, parameter, sub_sub_cancel]
    field_simp
    ring
  · unfold cubic slopeD
    rw [pullD_sub_one h]
    simp only [pullD, d, parameter, sub_sub_cancel]
    field_simp
    ring

/-- The two lifts on the actual cubics act on dx/y by the same overall
factors as the four normalized sources. The signs at the insertions are
recorded by half_differential_signs. -/
theorem chart_lifts {z : ℝ} (hz : 0 < z) (hz1 : z < 1) {x y : ℂ}
    (hx : (z : ℂ) * x - 1 ≠ 0) (hy : y ^ 2 = cubic .A z x) (hy0 : y ≠ 0) :
    let db := deriv (pullB z) x
    let dd := deriv (pullD z) x
    let yb := (-I * rootZ z) * db * y
    let yd := I * dd * y
    yb^2 = cubic .B z (pullB z x) ∧ yd^2 = cubic .D z (pullD z x) ∧
      1/y = (-I * rootZ z)*(db/yb) ∧ 1/y = I*(dd/yd) := by
  dsimp only
  have h0 : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have h1 : (1 : ℂ) - z ≠ 0 := by exact_mod_cast (sub_pos.mpr hz1).ne'
  have hb : (-I * rootZ z)^2 = -(z : ℂ) := by
    rw [mul_pow, neg_sq, Complex.I_sq, rootZ_sq hz, neg_one_mul]
  have hs := transition_slopes hx
  rw [hs.1.deriv, hs.2.deriv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [mul_pow, hb, hy] using (lifted_cubic h0 hx).1.symm
  · simpa only [mul_pow, Complex.I_sq, neg_one_mul, hy] using (lifted_cubic h0 hx).2.symm
  · have hs0 : slopeB z x ≠ 0 := div_ne_zero (mul_ne_zero h0 h1) (pow_ne_zero _ hx)
    have hr0 := rootZ_ne hz
    have hi := Complex.I_ne_zero
    field_simp
  · have hs0 : slopeD z x ≠ 0 := div_ne_zero h1 (pow_ne_zero _ hx)
    have hi := Complex.I_ne_zero
    field_simp

private def spatialNumerator (d x X : ℂ) : ℂ :=
  X*(X-1)*(x-d) + x*(x-1)*(X-d)

/-- Rational part of the J/T spatial differential, with the right leg
represented by rightChart. -/
def spatialKernel (d x X : ℂ) : ℂ :=
  spatialNumerator d x X / (2*(x-X)^2)

private theorem spatial_changes {z x X : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1)
    (hx : z * x - 1 ≠ 0) (hX : z * X - 1 ≠ 0) (hxx : x - X ≠ 0) :
    spatialKernel (d .A z) x X =
      -z⁻¹ * (spatialKernel (d .B z) (pullB z x) (pullB z X) + d .B z/2) ∧
    spatialKernel (d .A z) x X =
      -spatialKernel (d .D z) (pullD z x) (pullD z X) := by
  have hz' : z-1 ≠ 0 := sub_ne_zero.mpr hz1
  have hb : pullB z x - pullB z X = -z*(z-1)*(x-X)/((z*x-1)*(z*X-1)) := by
    unfold pullB
    field_simp
    ring
  have hd : pullD z x - pullD z X = -(z-1)*(x-X)/((z*x-1)*(z*X-1)) := by
    unfold pullD
    field_simp
    ring
  have hbnum : spatialNumerator (d .B z) (pullB z x) (pullB z X) =
      (-z^3*(z-1)^2 * spatialNumerator (d .A z) x X -
        (1-z)*z^2*(z-1)^2*(x-X)^2) / ((z*x-1)*(z*X-1))^2 := by
    unfold spatialNumerator
    rw [pullB_sub_one hx, pullB_sub_one hX]
    have hbd (t : ℂ) (ht : z * t - 1 ≠ 0) :
        pullB z t - d .B z = z*(z-1)*t/(z*t-1) := by
      simp only [pullB, d, parameter]
      field_simp
      ring
    rw [hbd x hx, hbd X hX]
    simp only [pullB, d, parameter, sub_sub_cancel, mul_pow]
    field_simp
    ring
  have hdnum : spatialNumerator (d .D z) (pullD z x) (pullD z X) =
      -(z-1)^2 * spatialNumerator (d .A z) x X / ((z*x-1)*(z*X-1))^2 := by
    unfold spatialNumerator
    rw [pullD_sub_one hx, pullD_sub_one hX]
    have hdd (t : ℂ) (ht : z * t - 1 ≠ 0) :
        pullD z t - d .D z = (z-1)/(z*(z*t-1)) := by
      simp only [pullD, d, parameter]
      field_simp
      ring
    rw [hdd x hx, hdd X hX]
    simp only [pullD, d, parameter, sub_sub_cancel, mul_pow]
    field_simp
    ring
  constructor
  · unfold spatialKernel
    rw [hb, hbnum]
    simp only [d, parameter, div_pow, mul_pow]
    field_simp
    ring
  · unfold spatialKernel
    rw [hd, hdnum]
    generalize hw : (z*x-1)*(z*X-1) = w
    have hw0 : w ≠ 0 := hw ▸ mul_ne_zero hx hX
    simp only [div_pow, mul_pow]
    field_simp

/-- With the relative puncture signs absorbed into the external variables,
the covariance discrepancy in the new differential units is constant in
both spatial variables. C is the period correction r(1-r)P'(r)/P(r). -/
theorem covariance_discrepancy {z : ℝ} (hz : 0 < z) (hz1 : z < 1) {x X : ℂ}
    (hx : (z : ℂ) * x - 1 ≠ 0) (hX : (z : ℂ) * X - 1 ≠ 0) (hxx : x - X ≠ 0)
    (C : ℂ → ℂ) :
    let zc : ℂ := z
    let old := spatialKernel (d .A zc) x X - C (parameter .A zc)
    let newB := spatialKernel (d .B zc) (pullB zc x) (pullB zc X) - C (parameter .B zc)
    let newD := spatialKernel (d .D zc) (pullD zc x) (pullD zc X) - C (parameter .D zc)
    (-I * rootZ z)^2 * old - newB = zc * C (parameter .A zc) + (1-zc)/2 + C zc ∧
    I^2 * old - newD = C (parameter .A zc) + C (parameter .D zc) := by
  dsimp only
  have h0 : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have h1 : (z : ℂ) ≠ 1 := by exact_mod_cast hz1.ne
  have h := spatial_changes h0 h1 hx hX hxx
  constructor
  · rw [h.1, mul_pow, neg_sq, Complex.I_sq, rootZ_sq hz, neg_one_mul]
    simp only [d, parameter]
    calc
      _ = ((z : ℂ) * (z : ℂ)⁻¹) *
          (spatialKernel (1-z) (pullB z x) (pullB z X) + (1-(z : ℂ))/2) +
          (z : ℂ) * C (1-(z : ℂ)⁻¹) -
          (spatialKernel (1-z) (pullB z x) (pullB z X) - C z) := by ring
      _ = _ := by rw [mul_inv_cancel₀ h0, one_mul]; ring
  · rw [h.2, Complex.I_sq]
    ring

open LatticeGeneratingFieldLocality LatticeHalfFock
open OriginalFourMChargeCoset (oscillatorLower)

/-- In each physical slot the raw input uses the inverse lowering
parameter. This identifies every factorial-normalized coefficient of
the actual polynomial action, with the same lift as the spatial source. -/
theorem puncture_lowering {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (D : LatticeData) (hu : IsUnit D.G.det) (c : Chart) (i : Puncture)
    (f : Oscillator D) (n : ℕ) :
    let eta := loweringParameter c i
    let lambda := scale c z i
    let root := scaleRoot c z i
    (∀ u, lambda+eta*u ≠ 0 → localCoordinate c z i (u/(lambda+eta*u)) = u) ∧
    root^2 = lambda ∧
    (-eta)^n • (scaleOscillator D root lambda)
        ((n.factorial : ℂ)⁻¹ • (oscillatorLower D^n) f) =
      (-eta)^n • (scaleOscillator D root lambda) (polynomialCoefficient D f n) := by
  dsimp only
  have hlambda := scale_ne hz hz1 c i
  refine ⟨?_, (chosen_roots hz hz1 c i).1, ?_⟩
  · intro u h
    rw [(local_coordinate_derivatives z c i).1]
    have he : 1 - loweringParameter c i * (u/(scale c z i + loweringParameter c i*u)) =
        scale c z i / (scale c z i + loweringParameter c i*u) := by
      field_simp
      ring
    rw [he]
    field_simp
    exact mul_div_cancel_right₀ u (by simpa only [mul_comm] using h)
  · rw [lowering_normal_order D hu]

/-- The same-orientation free covariance in each physical disk has the
actual regular half-current correction, with the very same local lift. -/
theorem puncture_cauchy_correction {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (c : Chart) (i : Puncture) {u v b c₀ : ℂ}
    (hb : b^2 = 1 - loweringParameter c i*u)
    (hc : c₀^2 = 1 - loweringParameter c i*v)
    (hb0 : b ≠ 0) (hc0 : c₀ ≠ 0) (hbc : b+c₀ ≠ 0) (huv : u ≠ v) :
    let root := scaleRoot c z i
    let fu := localCoordinate c z i u
    let fv := localCoordinate c z i v
    (root/b^3)*(root/c₀^3)*((fu+fv)/(2*(fu-fv)^2)) - (u+v)/(2*(u-v)^2) =
      loweringParameter c i*(1+b*c₀)/(2*b*c₀*(b+c₀)^2) := by
  dsimp only
  rw [(local_coordinate_derivatives z c i).1 u, (local_coordinate_derivatives z c i).1 v,
    ← hb, ← hc]
  exact regular_cauchy_correction (loweringParameter c i) (scale c z i) (scaleRoot c z i)
    u v b c₀ (chosen_roots hz hz1 c i).1 (scale_ne hz hz1 c i) hb hc hb0 hc0 hbc huv

open OriginalGaussianExternalBlocks (externalFreeEntry)

/-- For either native leg of each chart, the in/out covariance in the actual
free block sums to the mixed Cauchy subtraction. Colour pairing is the
separate Gram multiplier in explicitEffectiveKernel. -/
theorem mixed_free_covariance (D : LatticeData) (c : Chart) (right : Bool)
    (i j : Fin D.rank) {u v : ℂ} (h : ‖u*v‖ < 1) :
    let inward := if right then rightS c else leftP c
    let outward := if right then .S else leftQ c
    HasSum (fun n : ℕ =>
      externalFreeEntry D (outgoing c inward, i, n) (outgoing c outward, j, n) *
        (u*v)^n) (-(1+u*v)/(2*(1-u*v)^2)) := by
  dsimp only
  have hi : outgoing c (if right then rightS c else leftP c) = false := by
    cases c <;> cases right <;> rfl
  have ho : outgoing c (if right then .S else leftQ c) = true := by
    cases c <;> cases right <;> rfl
  rw [hi, ho]
  have hg : HasSum (fun n : ℕ => (u*v)^n) (1/(1-u*v)) := by
    simpa only [one_div] using hasSum_geometric_of_norm_lt_one h
  have hl := (hasSum_choose_mul_geometric_of_norm_lt_one 1 h).sub (hg.mul_left (1/2 : ℂ))
  have hne : 1-u*v ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    rw [← he, norm_one] at h
    exact (lt_irrefl _ h)
  convert hl.neg using 1
  · funext n
    simp [externalFreeEntry]
    ring
  · field_simp
    ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart
