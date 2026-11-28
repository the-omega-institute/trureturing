/- GID: D5/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/PerturbedCausalOrderWeyl4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vacuum plane wave curvature, its projective Weyl quartic, and exact null focusing. -/

import D5.S3.Geometry.Lorentz.WeylNullScreen
import D5.S3.Geometry.PPWaveDiamondMeasure
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! Exact curvature and optical geometry of a four-dimensional vacuum plane wave. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Lorentz.PerturbedCausalOrderWeyl4D

open WeylNullScreen Matrix Polynomial
open scoped BigOperators

abbrev Point := Fin 4 → ℝ

/-- Brinkmann coordinates are ordered as `(u,v,x,y)`. -/
def profile (A : ℝ) (p : Point) : ℝ := A * (p 2 ^ 2 - p 3 ^ 2)

def metric (A : ℝ) (p : Point) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![profile A p, -1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def metricInv (A : ℝ) (p : Point) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, 0, 0; -1, -profile A p, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem metric_inverse (A : ℝ) (p : Point) :
    metric A p * metricInv A p = 1 ∧ metricInv A p * metric A p = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [metric, metricInv, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]

theorem metric_det (A : ℝ) (p : Point) : (metric A p).det = -1 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, metric,
    Fin.castSucc, Fin.succ]

private def coordinateDeriv (i : Fin 4) (f : Point → ℝ) (p : Point) : ℝ :=
  deriv (fun t => f (Function.update p i t)) (p i)

private def delta (i j : Fin 4) : ℝ := if i = j then 1 else 0

private theorem update_deriv (p : Point) (i j : Fin 4) :
    HasDerivAt (fun t => Function.update p i t j) (delta i j) (p i) := by
  by_cases h : i = j
  · subst j
    simpa only [Function.update_self, delta, ite_true] using (hasDerivAt_id' (p i))
  · simpa [Function.update_of_ne (Ne.symm h), delta, h] using hasDerivAt_const (p i) (p j)

private def gradient (A : ℝ) (p : Point) (i : Fin 4) : ℝ :=
  2 * A * (delta i 2 * p 2 - delta i 3 * p 3)

private theorem partial_metric (A : ℝ) (p : Point) (i j k : Fin 4) :
    coordinateDeriv i (fun q => metric A q j k) p = delta j 0 * delta k 0 * gradient A p i := by
  have h := (((update_deriv p i 2).pow 2).sub ((update_deriv p i 3).pow 2)).const_mul A
  have hp : coordinateDeriv i (profile A) p = gradient A p i := by
    unfold coordinateDeriv profile
    convert h.deriv using 1
    simp [gradient]
    ring
  fin_cases j <;> fin_cases k <;> simp [metric, delta, coordinateDeriv] <;> exact hp

/-- Levi-Civita connection from the metric and its coordinate derivatives. -/
def christoffel (A : ℝ) (p : Point) (r a b : Fin 4) : ℝ :=
  (1 / 2) * ∑ d, metricInv A p r d *
    (coordinateDeriv a (fun q => metric A q d b) p + coordinateDeriv b (fun q => metric A q d a) p -
      coordinateDeriv d (fun q => metric A q a b) p)

theorem christoffel_eq (A : ℝ) (p : Point) (r a b : Fin 4) :
    christoffel A p r a b =
      -(delta r 1 * (delta a 0 * gradient A p b + delta b 0 * gradient A p a) +
        delta a 0 * delta b 0 * gradient A p r) / 2 := by
  fin_cases r <;>
    simp [christoffel, partial_metric, Fin.sum_univ_four, metricInv, delta, gradient, -ite_mul, -mul_ite] <;> ring

private def hessian (A : ℝ) (i j : Fin 4) : ℝ :=
  2 * A * (delta i 2 * delta j 2 - delta i 3 * delta j 3)

private theorem christoffel_deriv (A : ℝ) (p : Point) (i r a b : Fin 4) :
    coordinateDeriv i (fun q => christoffel A q r a b) p =
      -(delta r 1 * (delta a 0 * hessian A i b + delta b 0 * hessian A i a) +
        delta a 0 * delta b 0 * hessian A i r) / 2 := by
  have hg (j : Fin 4) : HasDerivAt (fun t => gradient A (Function.update p i t) j)
      (hessian A i j) (p i) := by
    convert (((update_deriv p i 2).const_mul (delta j 2)).sub
      ((update_deriv p i 3).const_mul (delta j 3))).const_mul (2 * A) using 1 <;>
      first | rfl | (unfold hessian; ring)
  unfold coordinateDeriv
  simp_rw [christoffel_eq]
  exact (((((hg b).const_mul (delta a 0)).add ((hg a).const_mul (delta b 0))).const_mul
    (delta r 1)).add ((hg r).const_mul (delta a 0 * delta b 0))).neg.div_const 2 |>.deriv

/-- Curvature in the convention `R^r_{sab} = ∂a Γ^r_{bs} - ∂b Γ^r_{as} + ⋯`. -/
def riemannUp (A : ℝ) (p : Point) (r s a b : Fin 4) : ℝ :=
  coordinateDeriv a (fun q => christoffel A q r b s) p -
    coordinateDeriv b (fun q => christoffel A q r a s) p +
    ∑ e, (christoffel A p r a e * christoffel A p e b s -
      christoffel A p r b e * christoffel A p e a s)

private theorem connection_products (A : ℝ) (p : Point) (r s a b : Fin 4) :
    (∑ e, (christoffel A p r a e * christoffel A p e b s -
      christoffel A p r b e * christoffel A p e a s)) = 0 := by
  rw [Fin.sum_univ_four]
  simp [christoffel_eq, gradient, delta, -ite_mul, -mul_ite] <;> ring

private theorem riemannUp_formula (A : ℝ) (p : Point) (r s a b : Fin 4) :
    riemannUp A p r s a b =
      (-delta r 1 * (delta b 0 * hessian A a s - delta a 0 * hessian A b s) -
        delta s 0 * (delta b 0 * hessian A a r - delta a 0 * hessian A b r)) / 2 := by
  rw [riemannUp, connection_products, christoffel_deriv, christoffel_deriv, add_zero]
  simp only [hessian]
  ring

def riemann (A : ℝ) (p : Point) (r s a b : Fin 4) : ℝ :=
  ∑ e, metric A p r e * riemannUp A p e s a b

private def wedgeCoord (j r s : Fin 4) : ℝ :=
  delta r 0 * delta s j - delta r j * delta s 0

theorem riemann_eq (A : ℝ) (p : Point) (r s a b : Fin 4) :
    riemann A p r s a b =
      -A * wedgeCoord 2 r s * wedgeCoord 2 a b + A * wedgeCoord 3 r s * wedgeCoord 3 a b := by
  fin_cases r <;>
    simp [riemann, riemannUp_formula, Fin.sum_univ_four, metric, hessian, wedgeCoord, delta, -ite_mul, -mul_ite] <;> ring

def ricciTensor (A : ℝ) (p : Point) (s b : Fin 4) : ℝ :=
  ∑ r, riemannUp A p r s r b

theorem ricci_zero (A : ℝ) (p : Point) (s b : Fin 4) : ricciTensor A p s b = 0 := by
  simp [ricciTensor, Fin.sum_univ_four, riemannUp_formula, hessian, delta, -ite_mul, -mul_ite] <;> ring

/-- Columns are the oriented orthonormal frame, with propagation along `e₀ + e₃`. -/
def frame (A : ℝ) (p : Point) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(√2)⁻¹, 0, 0, -(√2)⁻¹;
      (profile A p / 2 + 1) / √2, 0, 0, (1 - profile A p / 2) / √2;
      0, 1, 0, 0;
      0, 0, 1, 0]

private theorem sqrt_two_ne : (√(2 : ℝ)) ≠ 0 := by positivity

theorem frame_isometry (A : ℝ) (p : Point) :
    (frame A p)ᵀ * metric A p * frame A p = diagonal ![-1, 1, 1, 1] := by
  have hs : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [frame, metric, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
      Fin.sum_univ_four] <;>
    field_simp [sqrt_two_ne] <;> ring_nf <;> rw [hs] <;> norm_num

private def electricBlock (A : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-A / 2, 0, 0; 0, A / 2, 0; 0, 0, 0]

private def magneticBlock (A : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, A / 2, 0; A / 2, 0, 0; 0, 0, 0]

def waveWeyl (A : ℝ) : Weyl4 :=
  weyl_electric_magnetic_equiv.symm
    (⟨electricBlock A, ⟨by intro i j; fin_cases i <;> fin_cases j <;> rfl,
       by change (∑ i : Fin 3, 1 * electricBlock A i i) = 0
          simp [electricBlock, Fin.sum_univ_three] <;> ring⟩⟩,
     ⟨magneticBlock A, ⟨by intro i j; fin_cases i <;> fin_cases j <;> rfl,
       by change (∑ i : Fin 3, 1 * magneticBlock A i i) = 0
          simp [magneticBlock, Fin.sum_univ_three]⟩⟩)

private theorem wave_blocks (A : ℝ) :
    (waveWeyl A).val.val =
      fromBlocks (electricBlock A) (magneticBlock A) (magneticBlock A) (-electricBlock A) := rfl

private def pairIndices : PairIndex → Fin 4 × Fin 4
  | .inl i => (0, i.succ)
  | .inr i => (![2, 3, 1] i, ![3, 1, 2] i)

private def frameWedge (A : ℝ) (p : Point) (j : Fin 4) (i : PairIndex) : ℝ :=
  let (a, b) := pairIndices i
  frame A p 0 a * frame A p j b - frame A p j a * frame A p 0 b

private theorem frameWedge_table (A : ℝ) (p : Point) (i : PairIndex) :
    frameWedge A p 2 i = (√2)⁻¹ * i.elim ![1, 0, 0] ![0, -1, 0] ∧
    frameWedge A p 3 i = (√2)⁻¹ * i.elim ![0, 1, 0] ![1, 0, 0] := by
  rcases i with i | i <;> fin_cases i <;>
    norm_num [frameWedge, pairIndices, frame]

/-- The Weyl tensor is the computed coordinate curvature in the oriented pair basis. -/
theorem waveWeyl_pairMatrix (A : ℝ) (p : Point) (i j : PairIndex) :
    (waveWeyl A).val.val i j =
      ∑ r, ∑ s, ∑ a, ∑ b, riemann A p r s a b *
        frame A p r (pairIndices i).1 * frame A p s (pairIndices i).2 *
        frame A p a (pairIndices j).1 * frame A p b (pairIndices j).2 := by
  have wedge_sum (k : Fin 4) (x y : Fin 4) :
      (∑ r, ∑ s, wedgeCoord k r s * frame A p r x * frame A p s y) =
        frame A p 0 x * frame A p k y - frame A p k x * frame A p 0 y := by
    simp only [wedgeCoord, sub_mul, Finset.sum_sub_distrib]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    simp [delta, ite_mul, Finset.sum_ite_eq']
  have h (k : Fin 4) (B : ℝ) :
      (∑ r, ∑ s, ∑ a, ∑ b, B * wedgeCoord k r s * wedgeCoord k a b *
        frame A p r (pairIndices i).1 * frame A p s (pairIndices i).2 *
        frame A p a (pairIndices j).1 * frame A p b (pairIndices j).2) =
        B * frameWedge A p k i * frameWedge A p k j := by
    have hleft : frameWedge A p k i =
        ∑ r, ∑ s, wedgeCoord k r s * frame A p r (pairIndices i).1 *
          frame A p s (pairIndices i).2 :=
      (wedge_sum k (pairIndices i).1 (pairIndices i).2).symm
    have hright : frameWedge A p k j =
        ∑ a, ∑ b, wedgeCoord k a b * frame A p a (pairIndices j).1 *
          frame A p b (pairIndices j).2 :=
      (wedge_sum k (pairIndices j).1 (pairIndices j).2).symm
    rw [hleft, hright]
    conv_rhs =>
      lhs
      simp only [Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    congr! 4 <;> ring
  simp_rw [riemann_eq, add_mul, Finset.sum_add_distrib]
  rw [h 2 (-A), h 3 A, (frameWedge_table A p i).1, (frameWedge_table A p j).1,
    (frameWedge_table A p i).2, (frameWedge_table A p j).2, wave_blocks]
  have hs : ((√(2 : ℝ))⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    norm_num [electricBlock, magneticBlock, fromBlocks] <;>
    ring_nf <;> rw [hs] <;> ring

private def screenWedge (ray : FutureNullRay) (i : PairIndex) : ℂ :=
  let (a, b) := pairIndices i
  screenVector ray a * (nullGenerator ray b : ℂ) -
    screenVector ray b * (nullGenerator ray a : ℂ)

private theorem finite_screen (z : ℂ) (i : Fin 3) :
    screenWedge (some z) (.inl i) =
      ![z ^ 2 - 1, -Complex.I * (z ^ 2 + 1), 2 * z] i ∧
    screenWedge (some z) (.inr i) =
      -Complex.I * ![z ^ 2 - 1, -Complex.I * (z ^ 2 + 1), 2 * z] i := by
  fin_cases i <;> constructor <;> apply Complex.ext <;>
    norm_num [screenWedge, pairIndices, screenVector, nullGenerator, Complex.normSq_apply,
      pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.add_im,
      Complex.sub_im, Complex.mul_im] <;> ring

theorem wave_quartic (A : ℝ) :
    ((weylQuarticEquiv (waveWeyl A) : WeylQuartic) : ℂ[X]) =
      C (-4 * (A : ℂ)) * X ^ 4 := by
  apply Polynomial.funext
  intro z
  change quarticEval (some z) (weylQuarticEquiv (waveWeyl A)) = _
  rw [weylQuarticEquiv_eval]
  change (∑ i : PairIndex, ∑ j : PairIndex, ((waveWeyl A).val.val i j : ℂ) *
    screenWedge (some z) i * screenWedge (some z) j) = _
  simp only [wave_blocks, Fintype.sum_sum_type, Fin.sum_univ_three, (finite_screen z _).1,
    (finite_screen z _).2, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.neg_apply]
  norm_num [electricBlock, magneticBlock, Polynomial.eval_mul, Polynomial.eval_pow]
  ring_nf
  rw [show Complex.I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Complex.I_sq]; norm_num,
    Complex.I_sq]
  ring

theorem wave_typeN (A : ℝ) (hA : A ≠ 0) (p : Point) :
    (∀ z : ℂ, quarticEval (some z) (weylQuarticEquiv (waveWeyl A)) = 0 ↔ z = 0) ∧
    quarticEval none (weylQuarticEquiv (waveWeyl A)) ≠ 0 ∧
    (((weylQuarticEquiv (waveWeyl A) : WeylQuartic) : ℂ[X]).rootMultiplicity 0 = 4) ∧
    frame A p *ᵥ nullGenerator (some 0) = ![0, √2, 0, 0] := by
  have hc : (-4 * (A : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast hA)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    change (((weylQuarticEquiv (waveWeyl A) : WeylQuartic) : ℂ[X]).eval z = 0) ↔ _
    rw [wave_quartic]
    simp [hA]
  · change (((weylQuarticEquiv (waveWeyl A) : WeylQuartic) : ℂ[X]).coeff 4 ≠ 0)
    simpa only [wave_quartic, Polynomial.coeff_C_mul_X_pow, ite_eq_left rfl, ite_true] using hc
  · rw [wave_quartic]
    simpa only [map_zero, sub_zero, Polynomial.rootMultiplicity_C, zero_add] using
      (Polynomial.rootMultiplicity_mul_X_sub_C_pow
        (p := C (-4 * (A : ℂ))) (a := 0) (n := 4) (by simpa using hc))
  · have hs : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    funext i
    fin_cases i <;> norm_num [frame, nullGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      field_simp [sqrt_two_ne] <;> ring_nf <;> rw [hs] <;> norm_num

open Real

/-- The two solutions with arbitrary initial transverse position and velocity. -/
def waveX (ω x α t : ℝ) : ℝ := x * cosh (ω * t) + α * sinh (ω * t) / ω

def waveY (ω y β t : ℝ) : ℝ := y * cos (ω * t) + β * sin (ω * t) / ω

private def velocityX (ω x α t : ℝ) := x * ω * sinh (ω * t) + α * cosh (ω * t)
private def velocityY (ω y β t : ℝ) := -y * ω * sin (ω * t) + β * cos (ω * t)

private theorem waveX_deriv {ω : ℝ} (hω : ω ≠ 0) (x α t : ℝ) :
    HasDerivAt (waveX ω x α) (velocityX ω x α t) t := by
  have d : HasDerivAt (fun u : ℝ => ω * u) ω t := by
    simpa [id] using (hasDerivAt_id t).const_mul ω
  unfold waveX velocityX
  convert ((d.cosh.const_mul x).add ((d.sinh.const_mul α).div_const ω)) using 1
  field_simp <;> ring

private theorem waveY_deriv {ω : ℝ} (hω : ω ≠ 0) (y β t : ℝ) :
    HasDerivAt (waveY ω y β) (velocityY ω y β t) t := by
  have d : HasDerivAt (fun u : ℝ => ω * u) ω t := by
    simpa [id] using (hasDerivAt_id t).const_mul ω
  unfold waveY velocityY
  convert ((d.cos.const_mul y).add ((d.sin.const_mul β).div_const ω)) using 1
  field_simp <;> ring

private theorem velocityX_deriv {ω : ℝ} (hω : ω ≠ 0) (x α t : ℝ) :
    HasDerivAt (velocityX ω x α) (ω ^ 2 * waveX ω x α t) t := by
  have d : HasDerivAt (fun u : ℝ => ω * u) ω t := by
    simpa [id] using (hasDerivAt_id t).const_mul ω
  unfold waveX velocityX
  convert (d.sinh.const_mul (x * ω)).add (d.cosh.const_mul α) using 1
  field_simp <;> ring

private theorem velocityY_deriv {ω : ℝ} (hω : ω ≠ 0) (y β t : ℝ) :
    HasDerivAt (velocityY ω y β) (-(ω ^ 2) * waveY ω y β t) t := by
  have d : HasDerivAt (fun u : ℝ => ω * u) ω t := by
    simpa [id] using (hasDerivAt_id t).const_mul ω
  unfold waveY velocityY
  convert (d.sin.const_mul (-y * ω)).add (d.cos.const_mul β) using 1
  field_simp <;> ring

/-- Null geodesic with affine coordinate `u = t` and initial data `(v,x,y,α,β)`. -/
def nullGeodesic (ω v x y α β t : ℝ) : Point :=
  ![t, v + (waveX ω x α t * velocityX ω x α t + waveY ω y β t * velocityY ω y β t -
        x * α - y * β) / 2,
    waveX ω x α t, waveY ω y β t]

/-- Coordinate velocity of the explicit null geodesic. -/
def nullGeodesicVelocity (ω x y α β t : ℝ) : Point :=
  ![1, (velocityX ω x α t ^ 2 + velocityY ω y β t ^ 2 +
          ω ^ 2 * (waveX ω x α t ^ 2 - waveY ω y β t ^ 2)) / 2,
    velocityX ω x α t, velocityY ω y β t]

/-- The geodesic satisfies the affine connection equation and has zero metric speed. -/
theorem nullGeodesic_spec {ω : ℝ} (hω : ω ≠ 0) (v x y α β t : ℝ) :
    let γ := nullGeodesic ω v x y α β
    let w := nullGeodesicVelocity ω x y α β
    γ 0 = ![0, v, x, y] ∧ w 0 2 = α ∧ w 0 3 = β ∧
    (∀ r, HasDerivAt (fun u => γ u r) (w t r) t) ∧
    (∀ r, HasDerivAt (fun u => w u r)
      (-(∑ a, ∑ b, christoffel (ω ^ 2) (γ t) r a b * w t a * w t b)) t) ∧
    (∑ r, ∑ s, metric (ω ^ 2) (γ t) r s * w t r * w t s) = 0 := by
  dsimp only
  have dx := waveX_deriv hω x α t
  have dy := waveY_deriv hω y β t
  have ddx := velocityX_deriv hω x α t
  have ddy := velocityY_deriv hω y β t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [nullGeodesic, waveX, waveY, velocityX, velocityY] <;> ring
  · simp [nullGeodesicVelocity, velocityX]
  · simp [nullGeodesicVelocity, velocityY]
  · intro r
    fin_cases r
    · simpa [nullGeodesic, nullGeodesicVelocity] using (hasDerivAt_id' t)
    · change HasDerivAt (fun u => v + (waveX ω x α u * velocityX ω x α u +
        waveY ω y β u * velocityY ω y β u - x * α - y * β) / 2)
          ((velocityX ω x α t ^ 2 + velocityY ω y β t ^ 2 +
            ω ^ 2 * (waveX ω x α t ^ 2 - waveY ω y β t ^ 2)) / 2) t
      convert (((dx.mul ddx).add (dy.mul ddy)).sub_const (x * α)).sub_const (y * β)
        |>.div_const 2 |>.const_add v using 1 <;> ring
    · exact dx
    · exact dy
  · intro r
    fin_cases r
    · simp [nullGeodesicVelocity, christoffel_eq, delta, gradient, Fin.sum_univ_four, hasDerivAt_const]
    · simp [nullGeodesicVelocity, nullGeodesic, christoffel_eq, delta, gradient, Fin.sum_univ_four]
      convert (((ddx.pow 2).add (ddy.pow 2)).add
        (((dx.pow 2).sub (dy.pow 2)).const_mul (ω ^ 2))).div_const 2 using 1 <;> ring
    · convert ddx using 1 <;>
        simp [nullGeodesicVelocity, nullGeodesic, christoffel_eq, delta, gradient, Fin.sum_univ_four] <;> ring
    · convert ddy using 1 <;>
        simp [nullGeodesicVelocity, nullGeodesic, christoffel_eq, delta, gradient, Fin.sum_univ_four] <;> ring
  · simp [metric, profile, nullGeodesic, nullGeodesicVelocity, Fin.sum_univ_four]
    ring

private theorem ode_fundamental_pair {k : ℝ} (C S C' S' z z' : ℝ → ℝ)
    (hC : ∀ t, HasDerivAt C (C' t) t) (hS : ∀ t, HasDerivAt S (S' t) t)
    (hC' : ∀ t, HasDerivAt C' (k * C t) t) (hS' : ∀ t, HasDerivAt S' (k * S t) t)
    (hz : ∀ t, HasDerivAt z (z' t) t) (hz' : ∀ t, HasDerivAt z' (k * z t) t)
    (h0 : C 0 = 1 ∧ S 0 = 0 ∧ C' 0 = 0 ∧ S' 0 = 1) (t : ℝ) :
    z t = C t * z 0 + S t * z' 0 := by
  have invariant (f g f' g' : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
      (hg : ∀ t, HasDerivAt g (g' t) t) (hf' : ∀ t, HasDerivAt f' (k * f t) t)
      (hg' : ∀ t, HasDerivAt g' (k * g t) t) :
      f t * g' t - f' t * g t = f 0 * g' 0 - f' 0 * g 0 := by
    have d (u : ℝ) : HasDerivAt (fun v => f v * g' v - f' v * g v) 0 u := by
      convert ((hf u).mul (hg' u)).sub ((hf' u).mul (hg u)) using 1
      ring
    exact is_const_of_deriv_eq_zero (fun u => (d u).differentiableAt)
      (fun u => (d u).deriv) t 0
  have w := invariant C S C' S' hC hS hC' hS'
  have wC := invariant C z C' z' hC hz hC' hz'
  have wS := invariant z S z' S' hz hS hz' hS'
  obtain ⟨hC0, hS0, hC'0, hS'0⟩ := h0
  simp only [hC0, hS0, hC'0, hS'0, one_mul, zero_mul, mul_zero, mul_one, sub_zero]
    at w wC wS
  linear_combination (norm := ring) -z t * w + C t * wS + S t * wC

/-- Each transverse coordinate is determined by its displacement and velocity at zero. -/
theorem transverse_geodesic_unique {ω : ℝ} (hω : ω ≠ 0) (x y x' y' : ℝ → ℝ)
    (hx : ∀ t, HasDerivAt x (x' t) t) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hx' : ∀ t, HasDerivAt x' (ω ^ 2 * x t) t)
    (hy' : ∀ t, HasDerivAt y' (-(ω ^ 2) * y t) t) :
    x = waveX ω (x 0) (x' 0) ∧ y = waveY ω (y 0) (y' 0) := by
  constructor
  · funext t
    have h := ode_fundamental_pair (waveX ω 1 0) (waveX ω 0 1)
      (velocityX ω 1 0) (velocityX ω 0 1) x x'
      (waveX_deriv hω 1 0) (waveX_deriv hω 0 1)
      (velocityX_deriv hω 1 0) (velocityX_deriv hω 0 1) hx hx'
      (by simp [waveX, velocityX]) t
    rw [h]
    simp [waveX]
    <;> ring
  · funext t
    have h := ode_fundamental_pair (waveY ω 1 0) (waveY ω 0 1)
      (velocityY ω 1 0) (velocityY ω 0 1) y y'
      (waveY_deriv hω 1 0) (waveY_deriv hω 0 1)
      (velocityY_deriv hω 1 0) (velocityY_deriv hω 0 1) hy hy'
      (by simp [waveY, velocityY]) t
    rw [h]
    simp [waveY]
    <;> ring

def parallelJacobian (ω u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  diagonal ![cosh (ω * u), cos (ω * u)]

def vertexJacobian (ω u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  diagonal ![sinh (ω * u) / ω, sin (ω * u) / ω]

/-- The congruence with fixed transverse velocity and the vertex congruence are
linear in the respective position and velocity labels. -/
theorem transverse_jacobians (ω u x y α β : ℝ) :
    ![waveX ω x α u, waveY ω y β u] =
      parallelJacobian ω u *ᵥ ![x, y] + vertexJacobian ω u *ᵥ ![α, β] := by
  funext i
  fin_cases i <;> simp [waveX, waveY, parallelJacobian, vertexJacobian, mulVec,
    dotProduct, Fin.sum_univ_two, diagonal_apply] <;> ring

/-- The parallel congruence first loses rank at the quarter-turn of its oscillatory
coordinate. The remaining transverse image is the hyperbolic axis. -/
theorem parallel_first_caustic {ω : ℝ} (hω : 0 < ω) :
    (∀ u, 0 < u → u < π / (2 * ω) → 0 < (parallelJacobian ω u).det) ∧
    parallelJacobian ω (π / (2 * ω)) = diagonal ![cosh (π / 2), 0] ∧
    0 < cosh (π / 2) := by
  have hs : ω * (π / (2 * ω)) = π / 2 := by field_simp
  refine ⟨?_, by simp [parallelJacobian, hs], cosh_pos _⟩
  intro u hu h
  have h' : ω * u < π / 2 := by
    have h' := (lt_div_iff₀ (by positivity : 0 < 2 * ω)).mp h
    linarith
  simp [parallelJacobian, Matrix.det_diagonal, Fin.prod_univ_two]
  exact mul_pos (cosh_pos _) (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, mul_pos hω hu], h'⟩)

/-- The vertex congruence first loses rank after a half-turn of its oscillatory
coordinate. The remaining transverse image is the hyperbolic axis. -/
theorem vertex_first_caustic {ω : ℝ} (hω : 0 < ω) :
    (∀ u, 0 < u → u < π / ω → 0 < (vertexJacobian ω u).det) ∧
    vertexJacobian ω (π / ω) = diagonal ![sinh π / ω, 0] ∧
    0 < sinh π / ω := by
  have hs : ω * (π / ω) = π := by field_simp
  refine ⟨?_, by simp [vertexJacobian, hs], div_pos (Real.sinh_pos_iff.mpr pi_pos) hω⟩
  intro u hu h
  have h' : ω * u < π := by simpa [mul_comm] using (lt_div_iff₀ hω).mp h
  have hpos := mul_pos hω hu
  simp [vertexJacobian, Matrix.det_diagonal, Fin.prod_univ_two]
  exact mul_pos (div_pos (Real.sinh_pos_iff.mpr hpos) hω)
    (div_pos (sin_pos_of_pos_of_lt_pi hpos h') hω)

open scoped Topology
open Asymptotics

/-- The parallel screen area decreases strictly before the first caustic.
The vertex screen area is strictly smaller than the flat area at the same affine time. -/
theorem screen_area_contracts {ω u : ℝ} (hω : 0 < ω) (hu : 0 < u) :
    (u < π / (2 * ω) → 0 < (parallelJacobian ω u).det ∧ (parallelJacobian ω u).det < 1) ∧
    (u < π / ω → 0 < (vertexJacobian ω u).det ∧ (vertexJacobian ω u).det < u ^ 2) := by
  have hz := mul_pos hω hu
  constructor
  · intro hb
    have h : ω * u < π / 2 := by
      have := (lt_div_iff₀ (by positivity : 0 < 2 * ω)).mp hb
      linarith
    refine ⟨(parallel_first_caustic hω).1 u hu hb, ?_⟩
    simpa [parallelJacobian, Matrix.det_diagonal, Fin.prod_univ_two, mul_comm] using
      Omega.PPWaveDiamond.parallel_lt_one hz (show ω * u < π by linarith [pi_pos])
  · intro hb
    have h : ω * u < π := by simpa [mul_comm] using (lt_div_iff₀ hω).mp hb
    refine ⟨(vertex_first_caustic hω).1 u hu hb, ?_⟩
    simpa [vertexJacobian, Matrix.det_diagonal, Fin.prod_univ_two, div_mul_div_comm,
      ← pow_two, mul_comm, mul_pow, hω.ne'] using
      (div_lt_div_of_pos_right (Omega.PPWaveDiamond.vertex_lt_sq hz h)
        (show 0 < ω ^ 2 by positivity))

private def coneAreaNumerator (t : ℝ) : ℝ := sin t * sinh t

private theorem sin_jet_zero (n : ℕ) :
    iteratedDeriv n sin 0 = if n % 2 = 0 then 0 else (-1 : ℝ) ^ (n / 2) := by
  have hn : n = 2 * (n / 2) + n % 2 := by omega
  conv_lhs => rw [hn]
  by_cases h : n % 2 = 0
  · simp [h]
  · have h' : n % 2 = 1 := by omega
    simp [h', Real.iteratedDeriv_odd_sin]

private theorem sinh_jet_zero (n : ℕ) :
    iteratedDeriv n sinh 0 = if n % 2 = 0 then 0 else 1 := by
  have hn : n = 2 * (n / 2) + n % 2 := by omega
  conv_lhs => rw [hn]
  by_cases h : n % 2 = 0
  · simp [h]
  · have h' : n % 2 = 1 := by omega
    simp [h', Real.iteratedDeriv_odd_sinh]

private theorem cone_jet_zero (n : ℕ) :
    iteratedDeriv n coneAreaNumerator 0 =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (if i % 2 = 0 then 0 else (-1 : ℝ) ^ (i / 2)) *
        (if (n - i) % 2 = 0 then 0 else 1) := by
  unfold coneAreaNumerator
  rw [iteratedDeriv_fun_mul Real.contDiff_sin.contDiffAt Real.contDiff_sinh.contDiffAt]
  simp only [sin_jet_zero, sinh_jet_zero]

private theorem cone_taylor_six (t : ℝ) :
    taylorWithinEval coneAreaNumerator 6 Set.univ 0 t = t ^ 2 - t ^ 6 / 90 := by
  rw [taylor_within_apply]
  simp only [iteratedDerivWithin_univ, sub_zero, smul_eq_mul]
  norm_num [cone_jet_zero, Finset.sum_range_succ, Nat.choose, Nat.factorial]
  <;> ring

/-- The relative vertex area has fourth-order correction `-t^4 / 90`. -/
theorem vertex_area_asymptotic :
    (fun t : ℝ => sin t * sinh t / t ^ 2 - (1 - t ^ 4 / 90)) =o[𝓝[≠] (0 : ℝ)]
      (fun t => t ^ 4) := by
  have h := taylor_isLittleO_univ (f := coneAreaNumerator) (n := 6) (x₀ := 0)
    (Real.contDiff_sin.mul Real.contDiff_sinh)
  simp only [cone_taylor_six, sub_zero] at h
  have hlim := h.tendsto_div_nhds_zero.mono_left
    (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
  apply (isLittleO_iff_tendsto' _).mpr
  · apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    dsimp [coneAreaNumerator]
    field_simp
    <;> ring
  · filter_upwards [self_mem_nhdsWithin] with t ht hzero
    exact ((pow_ne_zero _ (show t ≠ 0 from ht)) hzero).elim

open MeasureTheory

private theorem metric_graph_speed (ω u v x y dx dy dv : ℝ) :
    let p : Point := ![u, v, x, y]
    let w : Point := ![1, dv, dx, dy]
    (∑ r, ∑ s, metric (ω ^ 2) p r s * w r * w s) =
      dx ^ 2 + dy ^ 2 + ω ^ 2 * (x ^ 2 - y ^ 2) - 2 * dv := by
  simp [metric, profile, Fin.sum_univ_four]
  ring

private def timelikeGraph (ω L : ℝ) (X Y V : ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 L, ∃ dx dy dv : ℝ,
    HasDerivAt X dx t ∧ HasDerivAt Y dy t ∧ HasDerivAt V dv t ∧
    let p : Point := ![t, V t, X t, Y t]
    let w : Point := ![1, dv, dx, dy]
    (∑ r, ∑ s, metric (ω ^ 2) p r s * w r * w s) < 0

/-- Future timelike reachability from an axial point. -/
def timelikeFromAxis (ω L x y v : ℝ) : Prop :=
  ∃ X Y V : ℝ → ℝ,
    X 0 = 0 ∧ Y 0 = 0 ∧ V 0 = 0 ∧ X L = x ∧ Y L = y ∧ V L = v ∧
    timelikeGraph ω L X Y V

/-- Future timelike reachability from a transverse point to the upper axial tip. -/
def timelikeToAxis (ω L x y v Vtip : ℝ) : Prop :=
  ∃ X Y V : ℝ → ℝ,
    X 0 = x ∧ Y 0 = y ∧ V 0 = v ∧ X L = 0 ∧ Y L = 0 ∧ V L = Vtip ∧
    timelikeGraph ω L X Y V

private theorem reflect_timelikeGraph {ω L : ℝ} {X Y V : ℝ → ℝ} (B : ℝ)
    (h : timelikeGraph ω L X Y V) :
    timelikeGraph ω L (fun t => X (L - t)) (fun t => Y (L - t)) (fun t => B - V (L - t)) := by
  intro t ht
  obtain ⟨dx, dy, dv, hx, hy, hv, hmetric⟩ :=
    h (L - t) ⟨sub_nonneg.mpr ht.2, sub_le_self L ht.1⟩
  have hi : HasDerivAt (fun t => L - t) (-1) t := (hasDerivAt_id' t).const_sub L
  refine ⟨-dx, -dy, dv, ?_, ?_, ?_, ?_⟩
  · simpa [Function.comp_def] using hx.comp t hi
  · simpa [Function.comp_def] using hy.comp t hi
  · simpa using (hv.comp t hi).const_sub B
  · simpa only [metric_graph_speed, neg_sq] using hmetric

theorem timelikeToAxis_iff (ω L x y v Vtip : ℝ) :
    timelikeToAxis ω L x y v Vtip ↔ timelikeFromAxis ω L x y (Vtip - v) := by
  constructor
  · rintro ⟨X, Y, V, hx₀, hy₀, hv₀, hx, hy, hv, h⟩
    refine ⟨_, _, _, ?_, ?_, ?_, ?_, ?_, ?_, reflect_timelikeGraph Vtip h⟩ <;>
      simp [hx₀, hy₀, hv₀, hx, hy, hv]
  · rintro ⟨X, Y, V, hx₀, hy₀, hv₀, hx, hy, hv, h⟩
    refine ⟨_, _, _, ?_, ?_, ?_, ?_, ?_, ?_, reflect_timelikeGraph Vtip h⟩ <;>
      simp [hx₀, hy₀, hv₀, hx, hy, hv]

private theorem reachable_iff (ω L x y v : ℝ) :
    timelikeFromAxis ω L x y v ↔ Omega.PPWaveDiamond.reachableFromAxis ω L x y v := by
  simp only [timelikeFromAxis, timelikeGraph, Omega.PPWaveDiamond.reachableFromAxis,
    metric_graph_speed, sub_lt_zero]

/-- The axial chronological diamond in product coordinates `(u,x,y,v)`.
The two timelike graphs meet at a point of the diamond. -/
def axialMetricDiamond (ω T V : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Set.Ioo 0 T ∧ timelikeFromAxis ω p.1 p.2.1 p.2.2.1 p.2.2.2 ∧
    timelikeToAxis ω (T - p.1) p.2.1 p.2.2.1 p.2.2.2 V}

/-- The exact coordinate four-volume of the vacuum diamond exceeds the flat value. -/
theorem axial_diamond_volume {ω T V : ℝ}
    (hω : 0 < ω) (hT : 0 < T) (hπ : ω * T < π) (hV : 0 < V) :
    volume (axialMetricDiamond ω T V) =
        ENNReal.ofReal (Omega.PPWaveDiamond.exactAxialVolume ω T V) ∧
      volume (axialMetricDiamond 0 T V) = ENNReal.ofReal (π * V ^ 2 * T ^ 2 / 6) ∧
      volume (axialMetricDiamond 0 T V) < volume (axialMetricDiamond ω T V) := by
  have h (a : ℝ) : axialMetricDiamond a T V = Omega.PPWaveDiamond.axialDiamond a T V := by
    ext p
    simp only [axialMetricDiamond, Omega.PPWaveDiamond.axialDiamond, Set.mem_ofPred_eq,
      timelikeToAxis_iff, reachable_iff]
  rw [h ω, h 0]
  exact ⟨Omega.PPWaveDiamond.volume_axialDiamond hω hT hπ hV,
    Omega.PPWaveDiamond.volume_axialDiamond_flat hT hV,
    Omega.PPWaveDiamond.volume_axialDiamond_flat_lt hω hT hπ hV⟩

end D5.S3.Geometry.Lorentz.PerturbedCausalOrderWeyl4D
