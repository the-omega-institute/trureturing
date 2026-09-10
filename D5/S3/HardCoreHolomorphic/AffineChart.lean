/- GID: D5/S3/HardCoreHolomorphic/AffineChart
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/AffineChart
   mirror-E: none(waiver:symbolic-holomorphic-identities)
   anchors: []
   digest: Explicit logarithmic message coordinates, exponential inverses and exact projective flow. -/

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.AffineChart

/-- The positive real message is extended as this affine complex polynomial. -/
def psi (a b x : ℂ) : ℂ := b - a * x

/-- A single logarithm suffices. On the positive real interval this is
`log (x / (b-a*x)) / b`. The principal branch is used only on the slit plane. -/
def chart (a b x : ℂ) : ℂ := -Complex.log (b / x - a) / b

/-- Explicit exponential inverse, valid also when `a=0`. -/
def inverse (a b m : ℂ) : ℂ :=
  b * Complex.exp (b * m) / (1 + a * Complex.exp (b * m))

/-- Real center of the complex neighborhood. -/
def center (a b x : ℝ) : ℂ := ((-Real.log (b / x - a) / b : ℝ) : ℂ)

/-- The inverse has the actual complex derivative `x*(b-a*x)`. -/
theorem inverse_hasDerivAt (a b m : ℂ)
    (hd : 1 + a * Complex.exp (b * m) ≠ 0) :
    HasDerivAt (inverse a b) (inverse a b m * psi a b (inverse a b m)) m := by
  have he := ((hasDerivAt_id m).const_mul b).cexp
  have h := (he.const_mul b).div ((he.const_mul a).const_add 1) hd
  convert! h using 1
  dsimp [inverse, psi]
  field_simp [hd, mul_comm]

/-- Actual holomorphic chart derivative, with branch and pole assumptions explicit. -/
theorem chart_hasDerivAt (a b x : ℂ) (hb : b ≠ 0) (hx : x ≠ 0)
    (hs : b / x - a ∈ Complex.slitPlane) :
    HasDerivAt (chart a b) (1 / (x * psi a b x)) x := by
  have hh : b / x - a ≠ 0 := Complex.slitPlane_ne_zero hs
  have hp : psi a b x ≠ 0 := by
    intro h
    apply hh
    dsimp [psi] at h
    field_simp [hx]
    linear_combination h
  have h := ((((hasDerivAt_const x b).div (hasDerivAt_id x) hx).sub_const a).clog hs).neg.div_const b
  convert! h using 1
  dsimp [chart, psi]
  field_simp [hb, hx, hh, hp]
  ring

/-- Exponentiating the real chart identifies the odds exactly. -/
theorem exp_center (a b x : ℝ) (hb : 0 < b) (hx : 0 < x) (hp : 0 < b-a*x) :
    Complex.exp ((b : ℂ) * center a b x) = ((x / (b-a*x) : ℝ) : ℂ) := by
  have hq : 0 < b / x - a := by
    exact (sub_pos.mpr ((lt_div_iff₀ hx).mpr (sub_pos.mp hp)))
  have he : b * (-Real.log (b / x-a) / b) = -Real.log (b / x-a) := by
    field_simp [ne_of_gt hb]
  have hr : Real.exp (b * (-Real.log (b/x-a)/b)) = x/(b-a*x) := by
    rw [he, Real.exp_neg, Real.exp_log hq]
    field_simp [ne_of_gt hx, ne_of_gt hp, ne_of_gt hq]
  simpa only [center, ← Complex.ofReal_mul, Complex.ofReal_exp] using congrArg Complex.ofReal hr

/-- The inverse returns every real interval point exactly. -/
theorem inverse_center (a b x : ℝ) (hb : 0 < b) (hx : 0 < x) (hp : 0 < b-a*x) :
    inverse a b (center a b x) = (x : ℂ) := by
  rw [inverse, exp_center a b x hb hx hp]
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  have hp' : ((b-a*x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  push_cast at hp' ⊢
  field_simp [hb', hp', mul_comm]
  ring

/-- Real chart and principal complex chart agree on the positive branch. -/
theorem center_eq_chart (a b x : ℝ) (hx : 0 < x) (hp : 0 < b-a*x) :
    center a b x = chart a b x := by
  have hq : 0 < b/x-a := (sub_pos.mpr ((lt_div_iff₀ hx).mpr (sub_pos.mp hp)))
  simp only [center, chart, ← Complex.ofReal_div, ← Complex.ofReal_sub,
    ← Complex.ofReal_log hq.le, ← Complex.ofReal_neg]

/-- The inverse is two-sided on the principal branch strip. This is the
local coordinate identity needed for genuine conjugation, rather than only
recovery of one real anchor. -/
theorem chart_inverse (a b m : ℂ) (hb : b ≠ 0)
    (hd : 1+a*Complex.exp (b*m) ≠ 0)
    (him : -Real.pi < (b*m).im ∧ (b*m).im < Real.pi) :
    chart a b (inverse a b m) = m := by
  have he : Complex.exp (b*m) ≠ 0 := Complex.exp_ne_zero _
  have hq : b / inverse a b m-a = Complex.exp (-(b*m)) := by
    rw [inverse, Complex.exp_neg]
    field_simp [hb,hd,he] <;> ring
  rw [chart,hq,Complex.log_exp (by simpa using neg_lt_neg him.2)
    (by simpa using (neg_lt_neg him.1).le)]
  field_simp [hb] <;> ring

/-- Projective odds are multiplied by the exponential under coordinate translation.
This identifies the exact representation that connects additive shifts and multiplication. -/
theorem inverse_odds (a b m : ℂ) (hb : b ≠ 0)
    (hd : 1+a*Complex.exp (b*m) ≠ 0) :
    inverse a b m / psi a b (inverse a b m) = Complex.exp (b*m) := by
  dsimp [inverse, psi]
  field_simp [hb, hd, mul_comm]
  ring

/-- The fractional-linear action of the matrix
`[[E,0],[k*(E-1),1]]` on its pole-free affine chart. -/
def projective (k E x : ℂ) : ℂ := E*x/(1+k*(E-1)*x)

/-- Projective flow obeys the multiplicative composition law on its pole-free chart. -/
theorem projective_mul (k E F x : ℂ)
    (hF : 1+k*(F-1)*x ≠ 0)
    (hEF : 1+k*(E*F-1)*x ≠ 0) :
    projective k E (projective k F x) = projective k (E*F) x := by
  have hd : 1+k*(E-1)*projective k F x ≠ 0 := by
    intro h
    apply hEF
    dsimp [projective] at h
    have hz := congrArg (fun z : ℂ => z*(1+k*(F-1)*x)) h
    field_simp (disch := first | assumption | (convert hF using 1; ring1)) at hz
    linear_combination hz
  dsimp [projective] at hd ⊢
  apply (div_eq_div_iff hd hEF).2
  field_simp (disch := first | assumption | (convert hF using 1; ring1))
  ring

/-- Distinct type ratios have a genuine noncommutative matrix defect.
The matrices are [[E,0],[k*(E-1),1]] and [[F,0],[l*(F-1),1]]. -/
theorem projective_matrix_defect (k l E F : ℂ) :
    (k*(E-1)*F+l*(F-1))-(l*(F-1)*E+k*(E-1)) =
      (k-l)*(E-1)*(F-1) := by ring

/-- Real shifts scale the odds modulus; imaginary shifts rotate its phase.
No probability-amplitude or quantum-measurement interpretation is assumed. -/
theorem odds_amplitude_phase (b u v : ℝ) :
    Complex.exp ((b:ℂ)*((u:ℂ)+(v:ℂ)*Complex.I)) =
      (Real.exp (b*u):ℂ) * Complex.exp (((b*v:ℝ):ℂ)*Complex.I) ∧
    ‖Complex.exp ((b:ℂ)*((u:ℂ)+(v:ℂ)*Complex.I))‖ = Real.exp (b*u) := by
  constructor
  · rw [show (b:ℂ)*((u:ℂ)+(v:ℂ)*Complex.I) =
        ((b*u:ℝ):ℂ)+((b*v:ℝ):ℂ)*Complex.I by push_cast; ring, Complex.exp_add]
    simp
  · simp [Complex.norm_exp]

#print axioms inverse_hasDerivAt
#print axioms chart_hasDerivAt
#print axioms exp_center
#print axioms inverse_center
#print axioms center_eq_chart
#print axioms chart_inverse
#print axioms inverse_odds
#print axioms projective_mul
#print axioms projective_matrix_defect
#print axioms odds_amplitude_phase
end D5.S3.HardCoreHolomorphic.AffineChart
