/- GID: D5/S3/Quantum/Semigroups/WuCubicHotInnerMixed
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicHotInnerMixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The physical one-mode mixed derivative and Hermitian trace for the Wu cubic deficit. -/

import D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import OmegaBuild.Commands

/-! The exact mixed cubic coefficient for the one-mode Gibbs embedding in
the hot inner region of Wu v1 (3.54), at cubic exponent and equal caps.
The spectral expression extends to signed real z near zero, where z = k²
on the physical locus. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed

def v (u b y : ℝ) : ℝ := u * (1 + b*y)
def w (a y : ℝ) : ℝ := 1 - a*y

def lower (u v w z : ℝ) : ℝ :=
  (v+w-Real.sqrt ((w-v)^2+4*u*z))/2

def upper (u v w z : ℝ) : ℝ :=
  (v+w+Real.sqrt ((w-v)^2+4*u*z))/2

def cubicLog (x : ℝ) : ℝ := 3*x^3*Real.log x

def cubicLogSlope (x : ℝ) : ℝ := 9*x^2*Real.log x+3*x^2

def spectral (u a b z y : ℝ) : ℝ :=
  cubicLog (lower u (v u b y) (w a y) z) +
  cubicLog (upper u (v u b y) (w a y) z)

private theorem cubicLog_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt cubicLog (cubicLogSlope x) x := by
  have h := ((hasDerivAt_pow 3 x).const_mul 3).mul (Real.hasDerivAt_log hx)
  convert h using 1
  all_goals first | rfl | (simp [cubicLogSlope, cubicLog]; field_simp [hx]; ring)

private theorem slope_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt cubicLogSlope (18*x*Real.log x+15*x) x := by
  have h := (((hasDerivAt_pow 2 x).const_mul 9).mul
    (Real.hasDerivAt_log hx)).add ((hasDerivAt_pow 2 x).const_mul 3)
  convert h using 1
  all_goals first | rfl | (simp [cubicLogSlope]; field_simp [hx]; ring)

private theorem lower_zero {u v w : ℝ} (h : v < w) :
    lower u v w 0 = v := by
  simp [lower, Real.sqrt_sq (sub_nonneg.mpr h.le)]
  <;> ring

private theorem upper_zero {u v w : ℝ} (h : v < w) :
    upper u v w 0 = w := by
  simp [upper, Real.sqrt_sq (sub_nonneg.mpr h.le)]
  <;> ring

private theorem lower_hasDerivAt {u v w : ℝ} (h : v < w) :
    HasDerivAt (lower u v w) (-u/(w-v)) 0 := by
  have hgap : 0 < w-v := sub_pos.mpr h
  have hd := ((hasDerivAt_id (0 : ℝ)).const_mul (4*u)).const_add ((w-v)^2)
  have hs := hd.sqrt (by simpa using pow_ne_zero 2 hgap.ne')
  have hh := (hs.const_sub (v+w)).div_const 2
  convert hh using 1
  all_goals first | rfl | (simp [lower, upper, Real.sqrt_sq hgap.le]; field_simp [hgap.ne']; ring)

private theorem upper_hasDerivAt {u v w : ℝ} (h : v < w) :
    HasDerivAt (upper u v w) (u/(w-v)) 0 := by
  have hgap : 0 < w-v := sub_pos.mpr h
  have hd := ((hasDerivAt_id (0 : ℝ)).const_mul (4*u)).const_add ((w-v)^2)
  have hs := hd.sqrt (by simpa using pow_ne_zero 2 hgap.ne')
  have hh := (hs.const_add (v+w)).div_const 2
  convert hh using 1
  all_goals first | rfl | (simp [lower, upper, Real.sqrt_sq hgap.le]; field_simp [hgap.ne']; ring)

private theorem spectral_z {u a b y : ℝ} (hv : 0 < v u b y)
    (hvw : v u b y < w a y) :
    HasDerivAt (fun z => spectral u a b z y)
      (u*(cubicLogSlope (w a y)-cubicLogSlope (v u b y))/(w a y-v u b y)) 0 := by
  have hl := (cubicLog_hasDerivAt
    (x := lower u (v u b y) (w a y) 0) (by rw [lower_zero hvw]; exact hv.ne')).comp
      0 (lower_hasDerivAt (u := u) hvw)
  have hu := (cubicLog_hasDerivAt
    (x := upper u (v u b y) (w a y) 0) (by rw [upper_zero hvw]; exact (hv.trans hvw).ne')).comp
      0 (upper_hasDerivAt (u := u) hvw)
  convert hl.add hu using 1
  all_goals first | rfl | (simp [Function.comp_def, spectral, lower_zero hvw, upper_zero hvw]; ring)

private theorem v_hasDerivAt (u b : ℝ) :
    HasDerivAt (v u b) (u*b) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).const_mul b).const_add 1).const_mul u
  convert h using 1 <;> first | rfl | ring

private theorem w_hasDerivAt (a : ℝ) :
    HasDerivAt (w a) (-a) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).const_mul a).const_sub 1)
  convert h using 1 <;> first | rfl | ring

def spectralMixed (u a b : ℝ) : ℝ :=
  u*((-15*a-u*b*(18*u*Real.log u+15*u))/(1-u) +
    (a+u*b)*(3-9*u^2*Real.log u-3*u^2)/(1-u)^2)

/-- The actual derivative of the z derivative of the spectral logarithm. -/
private theorem spectral_mixed (u a b : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt (fun y => deriv (fun z => spectral u a b z y) 0)
      (spectralMixed u a b) 0 := by
  have hv := v_hasDerivAt u b
  have hw := w_hasDerivAt a
  have hev : ∀ᶠ y in 𝓝 (0 : ℝ), 0 < v u b y :=
    continuousAt_const.eventually_lt hv.continuousAt (by simpa [v] using hu)
  have hew : ∀ᶠ y in 𝓝 (0 : ℝ), v u b y < w a y :=
    hv.continuousAt.eventually_lt hw.continuousAt (by simpa [v,w] using hu1)
  have hv' := (slope_hasDerivAt (x := v u b 0) (by simpa [v] using hu.ne')).comp 0 hv
  have hw' := (slope_hasDerivAt (x := w a 0) (by simp [w])).comp 0 hw
  have h := (((hw'.sub hv').const_mul u).div (hw.sub hv)
    (by simp [v,w]; linarith))
  have h' : HasDerivAt
      (fun y => u*(cubicLogSlope (w a y)-cubicLogSlope (v u b y))/(w a y-v u b y))
      (spectralMixed u a b) 0 := by
    convert h using 1
    all_goals first | rfl | (simp [Function.comp_def, spectralMixed, cubicLogSlope, v, w]; field_simp [show 1-u ≠ 0 by linarith]; ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [hev,hew] with y hp hlt
  exact (spectral_z hp hlt).deriv

/-- Cubic diagonal entries of the Gibbs embedding with z = k². -/
def diagonalLow (u a b z y : ℝ) : ℝ :=
  (v u b y)^3+u*z*(2*v u b y+w a y)

def diagonalHigh (u a b z y : ℝ) : ℝ :=
  (w a y)^3+u*z*(v u b y+2*w a y)

def mass (u a b z y : ℝ) : ℝ :=
  diagonalLow u a b z y + diagonalHigh u a b z y

/-- The explicit energy trace Tr(V² W), including its z-linear part. -/
def energy (u a b z y : ℝ) : ℝ :=
  2*u*b*y*((v u b y)^2+u*z) -
    2*a*y*((w a y)^2+u*z) + 2*u*z*(v u b y+w a y)

def charges (u a b z y : ℝ) : ℝ :=
  mass u a b z y * Real.log (mass u a b z y) +
    diagonalLow u a b z y * Real.log a +
    diagonalHigh u a b z y * Real.log b

def chargeMixed (u a b : ℝ) : ℝ :=
  u*(3*(u*b-a)+3*(2*u*b-a)*Real.log u)

private theorem mass_z (u a b y : ℝ) :
    HasDerivAt (fun z => mass u a b z y) (3*u*(v u b y+w a y)) 0 := by
  have h1 := (((hasDerivAt_id (0 : ℝ)).const_mul u).mul_const
    (2*v u b y+w a y)).const_add ((v u b y)^3)
  have h2 := (((hasDerivAt_id (0 : ℝ)).const_mul u).mul_const
    (v u b y+2*w a y)).const_add ((w a y)^3)
  convert h1.add h2 using 1 <;> first | rfl | ring | (funext x; simp [mass, diagonalLow, diagonalHigh]; ring)

private theorem charges_z {u a b y : ℝ} (ht : mass u a b 0 y ≠ 0) :
    HasDerivAt (fun z => charges u a b z y)
      (3*u*(v u b y+w a y)*(Real.log (mass u a b 0 y)+1) +
        u*(2*v u b y+w a y)*Real.log a +
        u*(v u b y+2*w a y)*Real.log b) 0 := by
  have hm := mass_z u a b y
  have h1 := (hm.mul (hm.log ht))
  have h2 := ((((hasDerivAt_id (0 : ℝ)).const_mul u).mul_const
    (2*v u b y+w a y)).const_add ((v u b y)^3)).mul_const (Real.log a)
  have h3 := ((((hasDerivAt_id (0 : ℝ)).const_mul u).mul_const
    (v u b y+2*w a y)).const_add ((w a y)^3)).mul_const (Real.log b)
  convert (h1.add h2).add h3 using 1
  all_goals first
  | rfl
  | (rw [mul_comm (mass u a b 0 y), div_mul_cancel₀ _ ht]; ring)
  | (funext x; simp [charges, diagonalLow, diagonalHigh]; ring)

private theorem mass_y (u a b : ℝ) (ha : a=u^3*b) :
    HasDerivAt (fun y => mass u a b 0 y) 0 0 := by
  have h := ((v_hasDerivAt u b).pow 3).add ((w_hasDerivAt a).pow 3)
  convert h using 1
  · funext y
    simp [mass,diagonalLow,diagonalHigh]
  · simp [v,w,ha]
    ring

/-- The mass normalization and both diagonal Gibbs logarithms, differentiated
as actual functions of the two variables. -/
private theorem charges_mixed (u a b : ℝ) (hu : 0 < u) (hb : 0 < b)
    (ha : a = u^3*b) (hn : b*(1+u^3)=1) :
    HasDerivAt (fun y => deriv (fun z => charges u a b z y) 0)
      (chargeMixed u a b) 0 := by
  have ht : mass u a b 0 0 = 1/b := by
    simp [mass,diagonalLow,diagonalHigh,v,w]
    rw [← one_div]
    apply (eq_div_iff hb.ne').2
    nlinarith [hn]
  have htn : mass u a b 0 0 ≠ 0 := by rw [ht]; positivity
  have hm := mass_y u a b ha
  have he : ∀ᶠ y in 𝓝 (0 : ℝ), 0 < mass u a b 0 y :=
    continuousAt_const.eventually_lt hm.continuousAt (by rw [ht]; positivity)
  have hv := v_hasDerivAt u b
  have hw := w_hasDerivAt a
  have hlog := (hm.log htn).add_const 1
  have hc1 := (((hv.add hw).const_mul (3*u)).mul hlog)
  have hc2 := (((hv.const_mul 2).add hw).const_mul u).mul_const (Real.log a)
  have hc3 := ((hv.add (hw.const_mul 2)).const_mul u).mul_const (Real.log b)
  have hloga : Real.log a = 3*Real.log u+Real.log b := by
    rw [ha, Real.log_mul (pow_ne_zero _ hu.ne') hb.ne', Real.log_pow]
    norm_num
  have hlogt : Real.log (mass u a b 0 0) = -Real.log b := by
    rw [ht, Real.log_div one_ne_zero hb.ne', Real.log_one, zero_sub]
  have h' : HasDerivAt
      (fun y => 3*u*(v u b y+w a y)*(Real.log (mass u a b 0 y)+1) +
        u*(2*v u b y+w a y)*Real.log a +
        u*(v u b y+2*w a y)*Real.log b) (chargeMixed u a b) 0 := by
    convert (hc1.add hc2).add hc3 using 1
    all_goals first | rfl | (simp [chargeMixed, hloga,hlogt,v,w]; ring) | (funext y; ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [he] with y hy
  exact (charges_z hy.ne').deriv

private theorem energy_z (u a b y : ℝ) :
    HasDerivAt (fun z => energy u a b z y)
      (2*u*b*y*u-2*a*y*u+2*u*(v u b y+w a y)) 0 := by
  have h1 := (((hasDerivAt_id (0 : ℝ)).const_mul u).const_add
    ((v u b y)^2)).const_mul (2*u*b*y)
  have h2 := (((hasDerivAt_id (0 : ℝ)).const_mul u).const_add
    ((w a y)^2)).const_mul (2*a*y)
  have h3 := ((hasDerivAt_id (0 : ℝ)).const_mul (2*u)).mul_const
    (v u b y+w a y)
  convert (h1.sub h2).add h3 using 1 <;> first | rfl | ring | (funext x; simp [energy]; ring)

private theorem energy_mixed (u a b : ℝ) :
    HasDerivAt (fun y => deriv (fun z => energy u a b z y) 0)
      (4*u*(u*b-a)) 0 := by
  have h1 := ((hasDerivAt_id (0 : ℝ)).const_mul (2*u*b)).mul_const u
  have h2 := ((hasDerivAt_id (0 : ℝ)).const_mul (2*a)).mul_const u
  have h3 := (((v_hasDerivAt u b).add (w_hasDerivAt a)).const_mul (2*u))
  have hh : HasDerivAt (fun y => 2*u*b*y*u-2*a*y*u+2*u*(v u b y+w a y))
      (4*u*(u*b-a)) 0 := by
    convert (h1.sub h2).add h3 using 1 <;> first | rfl | ring | (funext x; simp [energy]; ring)
  exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => (energy_z u a b y).deriv)

/-- The physical deficit after cancelling the common scale logarithm. -/
def deficit (u a b alpha z y : ℝ) : ℝ :=
  b*((9/8)*energy u a b z y-alpha*(spectral u a b z y-charges u a b z y))

private theorem raw_mixed (u a b alpha : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hb : 0 < b) (ha : a=u^3*b) (hn : b*(1+u^3)=1) :
    HasDerivAt (fun y => deriv (fun z => deficit u a b alpha z y) 0)
      (b*((9/8)*4*u*(u*b-a)-alpha*(spectralMixed u a b-chargeMixed u a b))) 0 := by
  have hv := v_hasDerivAt u b
  have hw := w_hasDerivAt a
  have hev : ∀ᶠ y in 𝓝 (0 : ℝ), 0 < v u b y :=
    continuousAt_const.eventually_lt hv.continuousAt (by simpa [v] using hu)
  have hew : ∀ᶠ y in 𝓝 (0 : ℝ), v u b y < w a y :=
    hv.continuousAt.eventually_lt hw.continuousAt (by simpa [v,w] using hu1)
  have hm := mass_y u a b ha
  have he : ∀ᶠ y in 𝓝 (0 : ℝ), 0 < mass u a b 0 y :=
    continuousAt_const.eventually_lt hm.continuousAt (by simp [mass,diagonalLow,diagonalHigh,v,w]; positivity)
  have hh := (((energy_mixed u a b).const_mul (9/8)).sub
    (((spectral_mixed u a b hu hu1).sub (charges_mixed u a b hu hb ha hn)).const_mul alpha)).const_mul b
  have h' : HasDerivAt (fun y => b*((9/8)*deriv (fun z => energy u a b z y) 0 -
      alpha*(deriv (fun z => spectral u a b z y) 0 - deriv (fun z => charges u a b z y) 0)))
      (b*((9/8)*4*u*(u*b-a)-alpha*(spectralMixed u a b-chargeMixed u a b))) 0 := by
    convert hh using 1 <;> first | rfl | ring | (funext x; ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [hev,hew,he] with y hpositive hlt ht
  have hs := spectral_z hpositive hlt
  have hc := charges_z (u := u) (a := a) (b := b) ht.ne'
  have hd := energy_z u a b y
  rw [hs.deriv,hc.deriv,hd.deriv]
  exact ((((hd.const_mul (9/8)).sub ((hs.sub hc).const_mul alpha)).const_mul b)).deriv

/-- Exact arithmetic comparison using the physical temperature identity. -/
private theorem mixed_eq (u a b alpha : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hb : 0 < b) (ha : a=u^3*b) (hn : b*(1+u^3)=1)
    (halpha : 4*alpha*Real.log u*(1+u+u^2)=3*u^2-3) :
    b*((9/8)*4*u*(u*b-a)-alpha*(spectralMixed u a b-chargeMixed u a b)) =
      -b*(9*a/4)*(1+u)/(1-u)*(2*(1-2*alpha)+2*(1-u)^2/(1+u+u^2)) := by
  have hgap : 1-u ≠ 0 := by linarith
  have hp : 1+u+u^2 ≠ 0 := by positivity
  rw [ha]
  have hfactor :
      b*((9/8)*4*u*(u*b-u^3*b)-alpha*(spectralMixed u (u^3*b) b-chargeMixed u (u^3*b) b)) -
      (-b*(9*(u^3*b)/4)*(1+u)/(1-u)*(2*(1-2*alpha)+2*(1-u)^2/(1+u+u^2))) =
      b^2*(3*u^2*(u^4+u^3-u^2+u+1))/(2*(1-u)^2*(1+u+u^2))*
        (4*alpha*Real.log u*(1+u+u^2)-3*u^2+3) := by
    unfold spectralMixed chargeMixed
    field_simp
    <;> ring
  rw [show 4*alpha*Real.log u*(1+u+u^2)-3*u^2+3=0 by linarith, mul_zero] at hfactor
  linarith only [hfactor]

/-- The temperature identity follows from Wu's physical coefficient. -/
private theorem physical_alpha_identity (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    4*WuRepeatedMiddleCubic.alpha (1/u)*Real.log u*(1+u+u^2)=3*u^2-3 := by
  have hr : 1 < 1/u := (lt_div_iff₀ hu).2 (by linarith)
  have hl : Real.log u ≠ 0 := (Real.log_neg hu hu1).ne
  have hlog : Real.log (1/u) = -Real.log u := by
    rw [Real.log_div one_ne_zero hu.ne',Real.log_one,zero_sub]
  have hp : (1/u)^2+1/u+1 ≠ 0 := by positivity
  rw [WuRepeatedMiddleCubic.alpha, if_neg hr.ne', hlog]
  field_simp
  <;> ring

/-- The exact coefficient of k²y, obtained by differentiating first in z=k²
and then in y at the scalar ray. -/
theorem hot_inner_mixed (u a b : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hb : 0 < b) (ha : a=u^3*b) (hn : b*(1+u^3)=1) :
    HasDerivAt (fun y => deriv (fun z =>
      deficit u a b (WuRepeatedMiddleCubic.alpha (1/u)) z y) 0)
      (-b*(9*a/4)*(1+u)/(1-u)*(2*(1-2*WuRepeatedMiddleCubic.alpha (1/u))+
        2*(1-u)^2/(1+u+u^2))) 0 := by
  have h := raw_mixed u a b (WuRepeatedMiddleCubic.alpha (1/u)) hu hu1 hb ha hn
  rw [mixed_eq u a b _ hu hu1 hb ha hn (physical_alpha_identity u hu hu1)] at h
  exact h

open Matrix Polynomial
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open private trace_cube_log from D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization
open D5.S3.Quantum.Information.PartialTraceMutualInformation (spectral_sum_eq_of_charpoly_prod)

/-- The complex Hermitian realization on the physical locus z=k². -/
def embedded (u a b k y : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v u b y : ℂ), (Real.sqrt u*k : ℝ); (Real.sqrt u*k : ℝ), (w a y : ℂ)]

def embeddedGenerator (u a b k y : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(2*u*b*y : ℝ), (Real.sqrt u*k : ℝ); (Real.sqrt u*k : ℝ), (-2*a*y : ℝ)]

private theorem embedded_hermitian (u a b k y : ℝ) :
    (embedded u a b k y).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedded, Matrix.conjTranspose_apply]

/-- The trace and the two diagonal entries of the matrix cubic give the
polynomial charges used in the derivative calculation. -/
private theorem embedded_cubic (u a b k y : ℝ) (hu : 0 ≤ u) :
    ((embedded u a b k y)^3) 0 0 = (diagonalLow u a b (k^2) y : ℂ) ∧
    ((embedded u a b k y)^3) 1 1 = (diagonalHigh u a b (k^2) y : ℂ) := by
  have hs := Real.sq_sqrt hu
  constructor <;>
    simp [embedded, diagonalLow, diagonalHigh, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, ← Complex.ofReal_mul, ← Complex.ofReal_add] <;>
    norm_cast <;> ring_nf <;> rw [hs] <;> ring

private theorem embedded_energy (u a b k y : ℝ) (hu : 0 ≤ u) :
    (((embedded u a b k y)^2 * embeddedGenerator u a b k y).trace).re =
      energy u a b (k^2) y := by
  have hs := Real.sq_sqrt hu
  simp [embedded, embeddedGenerator, energy, pow_succ, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.one_apply, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  <;> ring_nf <;> rw [hs] <;> ring

private theorem embedded_charpoly (u a b k y : ℝ) (hu : 0 ≤ u) :
    (embedded u a b k y).charpoly =
      ∏ i : Fin 2, (X - C ((![lower u (v u b y) (w a y) (k^2),
        upper u (v u b y) (w a y) (k^2)] : Fin 2 → ℝ) i : ℂ)) := by
  let V := v u b y
  let W := w a y
  let L := lower u V W (k^2)
  let U := upper u V W (k^2)
  have hs : 0 ≤ (W-V)^2 + 4*u*k^2 := by positivity
  have hs' := Real.sq_sqrt hs
  have hsum : L+U=V+W := by dsimp [L,U,lower,upper]; ring
  have hprod : L*U=V*W-u*k^2 := by
    dsimp [L,U,lower,upper]
    linear_combination -hs'/4
  have ht : (embedded u a b k y).trace = ((L+U : ℝ) : ℂ) := by
    rw [hsum]
    simp [embedded, Matrix.trace_fin_two,V,W]
  have hd : (embedded u a b k y).det = ((L*U : ℝ) : ℂ) := by
    rw [hprod]
    simp [embedded, Matrix.det_fin_two,V,W, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    norm_cast
    linear_combination k^2 * (Real.sq_sqrt hu)
  rw [Matrix.charpoly_fin_two, ht, hd, Fin.prod_univ_two]
  change X^2-C ((L+U : ℝ) : ℂ)*X+C ((L*U : ℝ) : ℂ) =
    (X-C (L : ℂ))*(X-C (U : ℂ))
  push_cast
  simp only [map_add,map_mul]
  ring

/-- The exact eigenvalue formula gives the ordinary trace entropy of the
embedded Hermitian matrix at every physical z=k². -/
theorem embedded_spectral (u a b k y : ℝ) (hu : 0 ≤ u) :
    ((embedded u a b k y)^3 * cfc Real.log ((embedded u a b k y)^3)).trace.re =
      spectral u a b (k^2) y := by
  rw [trace_cube_log (embedded_hermitian u a b k y)]
  have h := spectral_sum_eq_of_charpoly_prod (embedded_hermitian u a b k y)
    (![lower u (v u b y) (w a y) (k^2), upper u (v u b y) (w a y) (k^2)] : Fin 2 → ℝ)
    (fun x => x^3*Real.log (x^3)) (embedded_charpoly u a b k y hu)
  rw [h]
  simp [Fin.sum_univ_two, spectral, cubicLog, Real.log_pow]
  <;> ring

private theorem embedded_mass (u a b k y : ℝ) (hu : 0 ≤ u) :
    ((embedded u a b k y)^3).trace.re = mass u a b (k^2) y := by
  rw [Matrix.trace_fin_two, (embedded_cubic u a b k y hu).1,
    (embedded_cubic u a b k y hu).2]
  simp [mass]

/-- Ordinary-trace expression of the scaled one-mode deficit. -/
theorem embedded_deficit (u a b alpha k y : ℝ) (hu : 0 ≤ u) :
    deficit u a b alpha (k^2) y =
      b*((9/8)*(((embedded u a b k y)^2 * embeddedGenerator u a b k y).trace).re -
        alpha*(((embedded u a b k y)^3 * cfc Real.log ((embedded u a b k y)^3)).trace.re -
          (((embedded u a b k y)^3).trace.re *
            Real.log (((embedded u a b k y)^3).trace.re) +
            (((embedded u a b k y)^3) 0 0).re * Real.log a +
            (((embedded u a b k y)^3) 1 1).re * Real.log b))) := by
  rw [embedded_energy u a b k y hu, embedded_spectral u a b k y hu,
    embedded_mass u a b k y hu, (embedded_cubic u a b k y hu).1,
    (embedded_cubic u a b k y hu).2]
  simp [deficit, charges]

end D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed
