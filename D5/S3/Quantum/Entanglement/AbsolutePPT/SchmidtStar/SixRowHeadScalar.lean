/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.head_exists; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg
   digest: Same-vector scalar estimate for the exact K6 balanced-star head. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadScalar
open SixRowHeadPolynomial SixRowHeadCertificate
noncomputable section

/-- Squaring retains its direction because both compared roots are nonnegative. -/
private theorem square_bridge (s T W A Q V : ℝ)
    (hT : 0 < T) (hW : 0 < W) (hA : 0 < A) (hQ : 0 ≤ Q)
    (hV : V = A*T^2-s^4*W*T^2-Q^2)
    (hpoly : 0 ≤ 4*s^4*Q^2*(W*T^2)-V^2) :
    Real.sqrt A*T ≤ s^2*Real.sqrt (W*T^2)+Q := by
  have hR : 0 ≤ W*T^2 := by positivity
  have hr := Real.sq_sqrt hR
  have hterm : 0 ≤ 2*s^2*Q*Real.sqrt (W*T^2) := by positivity
  have hsq : V^2 ≤ (2*s^2*Q*Real.sqrt (W*T^2))^2 := by
    calc
      V^2 ≤ 4*s^4*Q^2*(W*T^2) := by linarith only [hpoly]
      _ = _ := by nlinarith only [congrArg (fun x : ℝ => 4*s^4*Q^2*x) hr]
  have hlin : V ≤ 2*s^2*Q*Real.sqrt (W*T^2) :=
    (le_abs_self V).trans ((sq_le_sq₀ (abs_nonneg V) hterm).mp
      (by simpa only [sq_abs] using hsq))
  have hs : A*T^2 ≤ (s^2*Real.sqrt (W*T^2)+Q)^2 := by
    nlinarith only [hV, hlin, congrArg (fun x : ℝ => s^4*x) hr]
  have hwr := Real.sq_sqrt hA.le
  apply (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt A*T) (by positivity)).mp
  nlinarith only [hs, congrArg (fun x : ℝ => x*T^2) hwr]

/-- The certificate controls the exact half-angle parametrization. -/
theorem half_angle_bound (z k h : ℝ) (hz : 0 < z) (hz' : z ≤ 3/4)
    (hk : 0 ≤ k) (hk' : k ≤ 1) (hh : 0 ≤ h) (hh' : h ≤ 3/2)
    (hg : 0 ≤ constraint z k h) :
    let s := (1-z^2)/(1+z^2)
    let t := 2*z/(1+z^2)
    let T := Real.sqrt (1+(2*s+s^2)*k)
    Real.sqrt (1+k*h+t^2*k) ≤
      s^2*Real.sqrt (1+k*h)+t^2*T+t^3*(1+s)*k*h/(2*T) := by
  let s := (1-z^2)/(1+z^2)
  let t := 2*z/(1+z^2)
  let T := Real.sqrt (1+(2*s+s^2)*k)
  change Real.sqrt (1+k*h+t^2*k) ≤
    s^2*Real.sqrt (1+k*h)+t^2*T+t^3*(1+s)*k*h/(2*T)
  have hD : 0 < 1+z^2 := by positivity
  have hs : 0 ≤ s := by dsimp [s]; apply div_nonneg _ hD.le; nlinarith
  have ht : 0 < t := by dsimp [t]; positivity
  have hT : 0 < T := by dsimp [T]; apply Real.sqrt_pos.mpr; positivity
  have hT2 : T^2 = 1+(2*s+s^2)*k := Real.sq_sqrt (by positivity)
  let W := 1+k*h
  have hW : 0 < W := by dsimp [W]; positivity
  let R := W*T^2
  let Q := t^2*T^2+t^3*(1+s)*k*h/2
  let V := (W+t^2*k)*T^2-s^4*R-Q^2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hid : (4*s^4*Q^2*R-V^2)*(1+z^2)^16 = numerator z k h := by
    dsimp only [V, R, Q, W]
    simp only [hT2]
    dsimp only [s, t, numerator]
    field_simp [ne_of_gt hD]
    <;> ring
  have hN : 0 ≤ numerator z k h := by
    rw [numerator_identity]
    exact mul_nonneg (by positivity) (polynomial_nonneg z k h hz.le hz' hk hk' hh hh' hg)
  have hpoly : 0 ≤ 4*s^4*Q^2*R-V^2 :=
    nonneg_of_mul_nonneg_left (by rw [hid]; exact hN) (by positivity)
  have hWV : 0 < W+t^2*k := by positivity
  have hbound := square_bridge s T W (W+t^2*k) Q V hT hW hWV hQ
    (by dsimp only [V,R]; ring) hpoly
  have hRroot : Real.sqrt R = Real.sqrt W*T := by
    dsimp [R]
    rw [Real.sqrt_mul hW.le, Real.sqrt_sq hT.le]
  have he : s^2*Real.sqrt R+Q =
      (s^2*Real.sqrt W+t^2*T+t^3*(1+s)*k*h/(2*T))*T := by
    rw [hRroot]
    dsimp only [Q]
    field_simp [ne_of_gt hT]
    <;> ring
  rw [he] at hbound
  exact (mul_le_mul_iff_left₀ hT).mp hbound

/-- A unit quarter-circle vector obeying the sorting cap satisfies the scalar bound. -/
theorem unit_bound (s t k h : ℝ) (hs : 0 ≤ s) (ht : 0 < t)
    (hn : s^2+t^2=1) (hk : 0 ≤ k) (hk' : k ≤ 1)
    (hh : 0 ≤ h) (hh' : h ≤ 3/2)
    (hcap : t^2 ≤ 4*s^2*(1+k*h)) :
    let T := Real.sqrt (1+(2*s+s^2)*k)
    Real.sqrt (1+k*h+t^2*k) ≤
      s^2*Real.sqrt (1+k*h)+t^2*T+t^3*(1+s)*k*h/(2*T) := by
  let z := t/(1+s)
  have h1s : 0 < 1+s := by positivity
  have hz : 0 < z := div_pos ht h1s
  have hz1 : z ≤ 1 := by
    apply (div_le_iff₀ h1s).mpr
    nlinarith
  have hD : 0 < 1+z^2 := by positivity
  have hsrep : s=(1-z^2)/(1+z^2) := by
    apply (eq_div_iff (ne_of_gt hD)).mpr
    dsimp [z]
    field_simp [ne_of_gt h1s]
    linear_combination (s+1)*hn
  have htrep : t=2*z/(1+z^2) := by
    apply (eq_div_iff (ne_of_gt hD)).mpr
    dsimp [z]
    field_simp [ne_of_gt h1s]
    nlinarith only [hn]
  have hg : 0 ≤ constraint z k h := by
    have he : constraint z k h = (1+z^2)^2*(s^2*(1+k*h)-t^2/4) := by
      simp only [hsrep, htrep]
      unfold constraint
      field_simp [ne_of_gt hD]
      <;> ring
    rw [he]
    exact mul_nonneg (sq_nonneg _) (by linarith only [hcap])
  have hz' : z ≤ 3/4 := by
    by_contra hz'
    have he := constraint_upper z k h (3/4) 1 (3/2) (by norm_num)
      (le_of_lt (lt_of_not_ge hz')) hz1 hk hk' hh hh'
    norm_num [constraint] at he
    dsimp only [constraint] at hg
    linarith only [he, hg]
  have hb := half_angle_bound z k h hz hz' hk hk' hh hh' hg
  simpa only [← hsrep, ← htrep] using hb

/-- The explicit normalized recipe, with no scalar premise left to a caller. -/
theorem recipe_bound (alpha k h : ℝ) (ha : 1/2 ≤ alpha)
    (hk : 0 ≤ k) (hk' : k ≤ 1) (hh : 0 ≤ h) (hh' : h ≤ 3/2) :
    let L := Real.sqrt (alpha^2+1+k*h)
    let s := alpha/L
    let t := Real.sqrt (1+k*h)/L
    let T := Real.sqrt (1+(2*s+s^2)*k)
    Real.sqrt (alpha^2+1+k+k*h) ≤
      alpha*s+t*T+t^2*(1+s)*k*h/(2*T) := by
  let W := 1+k*h
  let L := Real.sqrt (alpha^2+1+k*h)
  let s := alpha/L
  let t := Real.sqrt W/L
  let T := Real.sqrt (1+(2*s+s^2)*k)
  have hW : 0 < W := by dsimp [W]; positivity
  have hL : 0 < L := by dsimp [L]; apply Real.sqrt_pos.mpr; positivity
  have hL2 : L^2=alpha^2+W := by
    dsimp [L, W]
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hW2 := Real.sq_sqrt hW.le
  have hs : 0 ≤ s := div_nonneg (by linarith only [ha]) hL.le
  have ht : 0 < t := div_pos (Real.sqrt_pos.mpr hW) hL
  have hn : s^2+t^2=1 := by
    dsimp [s, t]
    field_simp [ne_of_gt hL]
    nlinarith only [hL2, hW2]
  have hT : 0 < T := by dsimp [T]; apply Real.sqrt_pos.mpr; positivity
  have hcap0 : W ≤ 4*alpha^2*W := by
    have halpha : 0 ≤ 4*alpha^2-1 := by
      nlinarith only [ha, sq_nonneg (alpha-1/2)]
    nlinarith only [mul_nonneg hW.le halpha]
  have hcap : t^2 ≤ 4*s^2*W := by
    have hd := div_le_div_of_nonneg_right hcap0 (sq_nonneg L)
    dsimp [s, t]
    rw [div_pow, hW2, div_pow]
    convert hd using 1 <;> ring
  have hb := unit_bound s t k h hs ht hn hk hk' hh hh' hcap
  change Real.sqrt (W+t^2*k) ≤
    s^2*Real.sqrt W+t^2*T+t^3*(1+s)*k*h/(2*T) at hb
  have he : s^2*Real.sqrt W+t^2*T+t^3*(1+s)*k*h/(2*T) =
      t*(alpha*s+t*T+t^2*(1+s)*k*h/(2*T)) := by
    dsimp only [s, t]
    field_simp [ne_of_gt hL, ne_of_gt hT]
    <;> ring
  have hr : t*Real.sqrt (alpha^2+1+k+k*h) = Real.sqrt (W+t^2*k) := by
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    have htL : t^2*L^2=W := by
      dsimp only [t]
      rw [div_pow]
      field_simp [ne_of_gt hL]
      exact hW2
    calc
      t^2*(alpha^2+1+k+k*h) = t^2*(L^2+k) := by rw [hL2]; dsimp [W]; ring
      _ = W+t^2*k := by rw [mul_add,htL]
  rw [he, ← hr] at hb
  exact (mul_le_mul_iff_right₀ ht).mp hb

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadScalar
