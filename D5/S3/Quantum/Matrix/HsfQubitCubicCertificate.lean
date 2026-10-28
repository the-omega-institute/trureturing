/- GID: D5/S3/Quantum/Matrix/HsfQubitCubicCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfQubitCubicCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Sqrt]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Matrix/HsfQubitCoupledScalar.coupled_cubic_le; premises=D5/S3/Quantum/Matrix/HsfQubitCubicCertificate.rectangular_J_nonneg
   digest: Exact endpoint positivity controls a coupled cubic residual on a rectangle. -/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-! The large-contrast scalar supplier for the complex two-dimensional cubic
coupling estimate associated with HSF #23103. The Bernstein coefficients are
rational or affine in sqrt(2); all identities and signs are checked by Lean.
No sampled numerical premise, arbitrary-dimensional HSF theorem, or novelty
claim is made. The original general HSF conjecture remains open.
The attempted information-escape audit is unresolved (IE-C050); see
https://github.com/the-omega-institute/trureturing/issues/23103. -/

@[expose] public section

noncomputable section
namespace D5.S3.Quantum.Matrix.HsfQubitCubicCertificate

/-- The excess of the cubic divided-difference mean over the geometric mean. -/
def e (t : ℝ) : ℝ := (1-t)^2*(2*t^2+t+2)/(3*(1+t^2))

/-- The cubic off-diagonal penalty in the normalization a=1, b=t^2. -/
def beta (t : ℝ) : ℝ :=
  2*(1-t^2)^2*(1+3*t^2+t^4)/(9*(1+t^2))

/-- The linear-quadratic term in the completed square. -/
def T (t y : ℝ) : ℝ := 4*e t*t*y+(e t)^2*y^2

/-- The residual after completing the square in the trace variable. -/
def J (t y : ℝ) : ℝ := 2*(1-2*t^2)*T t y+beta t*y^2-(9/4)*(T t y)^2

private def bernstein (q s : ℝ) : ℝ :=
  (4+(0)*s)*1*q^0*(1-q)^14 +
  (4/7+(2)*s)*14*q^1*(1-q)^13 +
  (-64/13+(496/91)*s)*91*q^2*(1-q)^12 +
  (-1181/91+(977/91)*s)*364*q^3*(1-q)^11 +
  (-97777/4004+(1681/91)*s)*1001*q^4*(1-q)^10 +
  (-14767/364+(237287/8008)*s)*2002*q^5*(1-q)^9 +
  (-39107/616+(14083/308)*s)*3003*q^6*(1-q)^8 +
  (-110257/1144+(948581/13728)*s)*3432*q^7*(1-q)^7 +
  (-990409/6864+(310598/3003)*s)*3003*q^8*(1-q)^6 +
  (-3447805/16016+(450053/2912)*s)*2002*q^9*(1-q)^5 +
  (-10328567/32032+(3713929/16016)*s)*1001*q^10*(1-q)^4 +
  (-1420197/2912+(1022051/2912)*s)*364*q^11*(1-q)^3 +
  (-83845/112+(391689/728)*s)*91*q^12*(1-q)^2 +
  (-131233/112+(187811/224)*s)*14*q^13*(1-q)^1 +
  (-60141/32+(21329/16)*s)*1*q^14*(1-q)^0

private theorem bernstein_nonneg (q s : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hs : 24 / 17 ≤ s) : 0 ≤ bernstein q s := by
  have hq' : 0 ≤ 1-q := by linarith
  have hc0 : 0 ≤ (4 : ℝ)+(0)*s := by linarith
  have hc1 : 0 ≤ (4/7 : ℝ)+(2)*s := by linarith
  have hc2 : 0 ≤ (-64/13 : ℝ)+(496/91)*s := by linarith
  have hc3 : 0 ≤ (-1181/91 : ℝ)+(977/91)*s := by linarith
  have hc4 : 0 ≤ (-97777/4004 : ℝ)+(1681/91)*s := by linarith
  have hc5 : 0 ≤ (-14767/364 : ℝ)+(237287/8008)*s := by linarith
  have hc6 : 0 ≤ (-39107/616 : ℝ)+(14083/308)*s := by linarith
  have hc7 : 0 ≤ (-110257/1144 : ℝ)+(948581/13728)*s := by linarith
  have hc8 : 0 ≤ (-990409/6864 : ℝ)+(310598/3003)*s := by linarith
  have hc9 : 0 ≤ (-3447805/16016 : ℝ)+(450053/2912)*s := by linarith
  have hc10 : 0 ≤ (-10328567/32032 : ℝ)+(3713929/16016)*s := by linarith
  have hc11 : 0 ≤ (-1420197/2912 : ℝ)+(1022051/2912)*s := by linarith
  have hc12 : 0 ≤ (-83845/112 : ℝ)+(391689/728)*s := by linarith
  have hc13 : 0 ≤ (-131233/112 : ℝ)+(187811/224)*s := by linarith
  have hc14 : 0 ≤ (-60141/32 : ℝ)+(21329/16)*s := by linarith
  unfold bernstein
  positivity

private def endpointPolynomial (t s : ℝ) : ℝ :=
  24*s*t*(1-2*t^2)*(2*t^2+t+2)*(1+t^2)^3 +
    4*(1-20*t^2)*(1-t)^2*(2*t^2+t+2)^2*(1+t^2)^2 +
    4*(1+t)^2*(1+3*t^2+t^4)*(1+t^2)^3 -
    12*s*t*(1-t)^4*(2*t^2+t+2)^3*(1+t^2) -
    (1-t)^6*(2*t^2+t+2)^4

private theorem bernstein_identity (t s : ℝ) (hs : s ^ 2 = 2) :
    bernstein (s*t) s = endpointPolynomial t s := by
  have hs3 : s^3 = 2*s := by
    calc
      s^3 = (s^2)^1*s := by ring
      _ = 2*s := by rw [hs]; norm_num
  have hs4 : s^4 = 4 := by
    calc
      s^4 = (s^2)^2 := by ring
      _ = 4 := by rw [hs]; norm_num
  have hs5 : s^5 = 4*s := by
    calc
      s^5 = (s^2)^2*s := by ring
      _ = 4*s := by rw [hs]; norm_num
  have hs6 : s^6 = 8 := by
    calc
      s^6 = (s^2)^3 := by ring
      _ = 8 := by rw [hs]; norm_num
  have hs7 : s^7 = 8*s := by
    calc
      s^7 = (s^2)^3*s := by ring
      _ = 8*s := by rw [hs]; norm_num
  have hs8 : s^8 = 16 := by
    calc
      s^8 = (s^2)^4 := by ring
      _ = 16 := by rw [hs]; norm_num
  have hs9 : s^9 = 16*s := by
    calc
      s^9 = (s^2)^4*s := by ring
      _ = 16*s := by rw [hs]; norm_num
  have hs10 : s^10 = 32 := by
    calc
      s^10 = (s^2)^5 := by ring
      _ = 32 := by rw [hs]; norm_num
  have hs11 : s^11 = 32*s := by
    calc
      s^11 = (s^2)^5*s := by ring
      _ = 32*s := by rw [hs]; norm_num
  have hs12 : s^12 = 64 := by
    calc
      s^12 = (s^2)^6 := by ring
      _ = 64 := by rw [hs]; norm_num
  have hs13 : s^13 = 64*s := by
    calc
      s^13 = (s^2)^6*s := by ring
      _ = 64*s := by rw [hs]; norm_num
  have hs14 : s^14 = 128 := by
    calc
      s^14 = (s^2)^7 := by ring
      _ = 128 := by rw [hs]; norm_num
  unfold bernstein endpointPolynomial
  ring_nf
  simp only [hs, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14]
  ring

private theorem endpoint_identity (t s : ℝ) (hs : s ^ 2 = 2) :
    9*(1+t^2)^4*J t s = (1-t)^2*endpointPolynomial t s := by
  have hd : 1+t^2 ≠ 0 := ne_of_gt (by positivity)
  have hs3 : s^3 = 2*s := by
    calc
      s^3 = s^2*s := by ring
      _ = 2*s := by rw [hs]
  have hs4 : s^4 = 4 := by
    calc
      s^4 = (s^2)^2 := by ring
      _ = 4 := by rw [hs]; norm_num
  unfold J T e beta endpointPolynomial
  field_simp [hd]
  ring_nf
  simp only [hs, hs3, hs4]
  ring

private theorem J_endpoint_nonneg (t : ℝ) (ht : 0 ≤ t) (ht2 : 2*t^2 ≤ 1) :
    0 ≤ J t (Real.sqrt 2) := by
  let s : ℝ := Real.sqrt 2
  have hs : s^2 = 2 := by dsimp [s]; norm_num
  have hspos : 0 < s := by dsimp [s]; positivity
  have hslow : (24/17 : ℝ) ≤ s := by nlinarith
  have hq : 0 ≤ s*t := by positivity
  have hq2 : (s*t)^2 ≤ 1 := by rw [mul_pow, hs]; exact ht2
  have hq1 : s*t ≤ 1 :=
    (sq_le_sq₀ hq (by norm_num : (0 : ℝ) ≤ 1)).mp (by simpa using hq2)
  have hp : 0 ≤ endpointPolynomial t s := by
    rw [← bernstein_identity t s hs]
    exact bernstein_nonneg (s*t) s hq hq1 hslow
  have hc : 0 ≤ 9*(1+t^2)^4*J t s := by
    rw [endpoint_identity t s hs]
    exact mul_nonneg (sq_nonneg _) hp
  exact nonneg_of_mul_nonneg_right hc (by positivity)

/-- The full closed rectangle is controlled, including zero off-diagonal
amplitude and the singular endpoint t^2=1/2. -/
theorem rectangular_J_nonneg (t y : ℝ) (ht : 0 ≤ t) (ht2 : 2*t^2 ≤ 1)
    (hy : 0 ≤ y) (hy2 : y^2 ≤ 2) : 0 ≤ J t y := by
  let s : ℝ := Real.sqrt 2
  let g : ℝ → ℝ := fun z =>
    8*(1-2*t^2)*e t*t +
    (beta t+2*(e t)^2*(1-20*t^2))*z -
    18*(e t)^3*t*z^2-(9/4)*(e t)^4*z^3
  have hs : s^2 = 2 := by dsimp [s]; norm_num
  have hspos : 0 < s := by dsimp [s]; positivity
  have hys : y ≤ s :=
    (sq_le_sq₀ hy (le_of_lt hspos)).mp (by simpa [hs] using hy2)
  have hsy : 0 ≤ s-y := sub_nonneg.mpr hys
  have hsy2 : 0 ≤ s^2-y^2 := by linarith
  have he : 0 ≤ e t := by unfold e; positivity
  have hd : 0 ≤ 1-2*t^2 := by linarith
  have hj (z : ℝ) : J t z = z*g z := by dsimp [J, T, g]; ring
  have hg0 : 0 ≤ g 0 := by
    simpa [g] using
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hd) he) ht
  have hgs : 0 ≤ g s := by
    have hend := J_endpoint_nonneg t ht ht2
    change 0 ≤ J t s at hend
    rw [hj] at hend
    exact nonneg_of_mul_nonneg_right hend hspos
  have hchord : 0 ≤ s*g y-y*g s-(s-y)*g 0 := by
    calc
      0 ≤ (18*(e t)^3*t)*s*y*(s-y) +
        ((9/4)*(e t)^4)*s*y*(s^2-y^2) := by positivity
      _ = s*g y-y*g s-(s-y)*g 0 := by dsimp [g]; ring
  have hproduct : 0 ≤ s*g y := by
    linarith [mul_nonneg hy hgs, mul_nonneg hsy hg0]
  rw [hj]
  exact mul_nonneg hy (nonneg_of_mul_nonneg_right hproduct hspos)

#print axioms rectangular_J_nonneg

end D5.S3.Quantum.Matrix.HsfQubitCubicCertificate

