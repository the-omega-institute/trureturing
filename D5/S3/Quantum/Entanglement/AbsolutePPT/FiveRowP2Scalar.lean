/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Full continuous scalar energy completion for the five-row P2 branch. -/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Uncompiled source candidate. Hyp is an explicit scalar relaxation, NOT a
physical definition of APPT. Its physical production is a separate obligation.
All intervals are closed and all variables real. No certificate-success premise. -/
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
noncomputable section

structure Hyp (r H D a q s : ℝ) : Prop where
  r0 : 0 ≤ r
  r1 : r ≤ 1/2
  H0 : 0 ≤ H
  D0 : 0 ≤ D
  a0 : 0 ≤ a
  q0 : 0 ≤ q
  s0 : 0 ≤ s
  mass : H+D+s = 5-10*r
  amin : H^2/9 ≤ a
  amax : a ≤ H^2
  qmin : D^2/14 ≤ q
  qbox : q ≤ D
  qmass : q ≤ D^2
  qcap : q ≤ 10/3
  coupled : a+2*r*H+10*r^2 ≤ (2-q/2)^2
  variance : (2/3)*(a-H^2/10)+(q-D^2/15) ≤ 4*s-(2/5)*s^2

def phi (q : ℝ) : ℝ := q-q^2/4
def W (r H D a q : ℝ) : ℝ := a+q+r*(H+D)
def B (r : ℝ) : ℝ := (19/25)*(1+3*r)*(5-10*r)
def B0 (r : ℝ) : ℝ := (4/5)*(1+3*r)*(5-10*r)
def mass (N j r H D : ℝ) : ℝ := N+j*r+H-D
def energy (N j r H D a q : ℝ) : ℝ :=
  (2+r)*mass N j r H D-N*(1+r)+W r H D a q

theorem quadratic_upper (A b c lo hi x K : ℝ) (hA : 0 ≤ A)
    (hx : lo ≤ x) (hx' : x ≤ hi)
    (hlo : A*lo^2+b*lo+c ≤ K) (hhi : A*hi^2+b*hi+c ≤ K) :
    A*x^2+b*x+c ≤ K := by
  by_cases he : lo=hi
  · have : x=lo := by linarith
    simpa [this] using hlo
  have hw : 0 < hi-lo := sub_pos.mpr (lt_of_le_of_ne (hx.trans hx') he)
  have h0 := mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hlo)
  have h1 := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hhi)
  have h2 := mul_nonneg hA (mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx'))
  have hmain : 0 ≤ (hi-lo)*(K-(A*x^2+b*x+c)) := by
    nlinarith only [h0,h1,mul_nonneg h2 hw.le]
  exact le_of_sub_nonneg (nonneg_of_mul_nonneg_right hmain hw)

theorem quadratic_lower (A b c lo hi x K : ℝ) (hA : A ≤ 0)
    (hx : lo ≤ x) (hx' : x ≤ hi)
    (hlo : K ≤ A*lo^2+b*lo+c) (hhi : K ≤ A*hi^2+b*hi+c) :
    K ≤ A*x^2+b*x+c := by
  have h := quadratic_upper (-A) (-b) (-c) lo hi x (-K)
    (neg_nonneg.mpr hA) hx hx' (by linarith) (by linarith)
  linarith

private theorem phi_lower (lo hi q K : ℝ) (hq : lo ≤ q) (hq' : q ≤ hi)
    (hlo : K ≤ phi lo) (hhi : K ≤ phi hi) : K ≤ phi q := by
  have hh := quadratic_lower (-1/4) 1 0 lo hi q K
    (by norm_num) hq hq' (by dsimp [phi] at hlo; linarith)
    (by dsimp [phi] at hhi; linarith)
  dsimp [phi]
  nlinarith only [hh]

theorem energy_envelopes {r H D a q s : ℝ} (h : Hyp r H D a q s) :
    a+q+2*r*H+10*r^2 ≤ 4-phi q ∧ a+q+2*r*H+10*r^2 ≤ 4 := by
  have hp : 0 ≤ phi q := by
    have := mul_nonneg h.q0 (show 0 ≤ 4-q by linarith [h.qcap])
    dsimp [phi]
    nlinarith [h.qcap]
  constructor <;> dsimp [phi] at * <;> nlinarith [h.coupled]

theorem pointwise_energy_cap {r H D a q s : ℝ} (h : Hyp r H D a q s) :
    W r H D a q ≤ B0 r := by
  have hmass : H+D ≤ 5-10*r := by linarith [h.mass,h.s0]
  have hD5 : D ≤ 5 := by nlinarith [h.H0,h.r0]
  have he := energy_envelopes h
  by_cases hlo : r ≤ 1/5
  · have need : r*(D-4+14*r) ≤ phi q := by
      by_cases hd : D ≤ 3
      · let K := max 0 (D/5-6/25)
        have hrhs : r*(D-4+14*r) ≤ K := by
          have hh := quadratic_upper 14 (D-4) 0 0 (1/5) r K (by norm_num)
            h.r0 hlo (by dsimp [K]; nlinarith [le_max_left (0:ℝ) (D/5-6/25)])
            (by dsimp [K]; nlinarith [le_max_right (0:ℝ) (D/5-6/25)])
          nlinarith only [hh]
        have hlow : K ≤ phi (D^2/14) := by
          have hD2 : D^2 ≤ 9 := by nlinarith [h.D0]
          have hD4 := mul_nonneg (sq_nonneg D) (show 0 ≤ 9-D^2 by linarith)
          have hl : (47/784)*D^2 ≤ phi (D^2/14) := by dsimp [phi]; nlinarith only [hD4]
          have hpos : 0 ≤ phi (D^2/14) := by nlinarith [sq_nonneg D]
          have hsq := sq_nonneg (D-392/235)
          have hs : D/5-6/25 ≤ (47/784)*D^2 := by nlinarith only [hsq]
          exact max_le hpos (hs.trans hl)
        have hhigh : K ≤ phi (10/3) := by dsimp [K,phi]; apply max_le <;> nlinarith
        exact hrhs.trans (phi_lower _ _ _ K h.qmin h.qcap hlow hhigh)
      · have hd3 : 3 ≤ D := le_of_not_ge hd
        have hrmax : r ≤ (5-D)/10 := by linarith [h.H0]
        have hrhs : r*(D-4+14*r) ≤ 9/25 := by
          have hh := quadratic_upper 14 (D-4) 0 0 ((5-D)/10) r (9/25)
            (by norm_num) h.r0 hrmax (by norm_num)
            (by nlinarith [mul_nonneg (show 0 ≤ D-3 by linarith) (show 0 ≤ 25-2*(D+3) by linarith)])
          nlinarith only [hh]
        have he0 : 9/14 ≤ D^2/14 := by nlinarith [h.D0]
        have he1 : D^2/14 ≤ 25/14 := by nlinarith [h.D0]
        have hlow : (9/25:ℝ) ≤ phi (D^2/14) := by
          have hh := phi_lower (9/14) (25/14) (D^2/14) (9/25) he0 he1
            (by norm_num [phi]) (by norm_num [phi])
          exact hh
        have hhigh : (9/25:ℝ) ≤ phi (10/3) := by norm_num [phi]
        exact hrhs.trans (phi_lower _ _ _ _ h.qmin h.qcap hlow hhigh)
    have hrH := mul_nonneg h.r0 h.H0
    dsimp [W,B0,phi] at *
    nlinarith
  · have hrlo : 1/5 ≤ r := le_of_not_ge hlo
    by_cases hmid : r ≤ 3/8
    · let c := (1+4*r)/2
      by_cases hh : c ≤ H
      · have hmul := mul_nonneg h.r0 (show 0 ≤ 5-10*r-H-D by linarith)
        have hmul' := mul_nonneg h.r0 (show 0 ≤ 2*H-(1+4*r) by dsimp [c] at hh; linarith)
        dsimp [W,B0] at *
        nlinarith
      · have hHc : H ≤ c := le_of_not_ge hh
        have hc0 : 0 ≤ c := by dsimp [c]; linarith [h.r0]
        have hend0 : (1-2*r)*(1-7*r) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith [h.r1]) (by linarith)
        have hendc : (3/4:ℝ)-9*r+18*r^2 ≤ 0 := by
          have hp := quadratic_upper 18 (-9) (3/4) (1/5) (3/8) r 0
            (by norm_num) hrlo hmid (by norm_num) (by norm_num)
          nlinarith only [hp]
        have hv := quadratic_upper 1 (-1) ((1+r)*(5-10*r)) 0 c H (B0 r)
          (by norm_num) h.H0 hHc
          (by dsimp [B0]; nlinarith only [hend0])
          (by dsimp [c,B0]; nlinarith only [hendc])
        have hmul := mul_nonneg (show 0 ≤ 1+r by linarith [h.r0])
          (show 0 ≤ 5-10*r-H-D by linarith)
        dsimp [W] at *
        nlinarith [h.amax,h.qbox]
    · have hrhigh : 3/8 ≤ r := le_of_not_ge hmid
      have hL0 : 0 ≤ H+D := add_nonneg h.H0 h.D0
      have hE : a+q ≤ (H+D)^2 := by nlinarith [h.amax,h.qmass,mul_nonneg h.H0 h.D0]
      have hm := mul_nonneg (show 0 ≤ (5-10*r)-(H+D) by linarith)
        (show 0 ≤ (5-10*r)+(H+D)+r by linarith [h.r0])
      have hp := mul_nonneg (show 0 ≤ 5-10*r by linarith [h.r1])
        (show 0 ≤ (4/5)*(1+3*r)-(5-9*r) by linarith)
      dsimp [W,B0] at *
      nlinarith

/-- Exact unnormalized energy cap. Zero u is handled before normalization;
there is no desired energy bound among the scalar premises. -/
theorem homogeneous_energy_cap (u v H D a q s : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hm : H+D+s=5*u-10*v) (ha' : a ≤ H^2) (hq' : q ≤ D^2)
    (hnorm : 0 < u → Hyp (v/u) (H/u) (D/u) (a/u^2) (q/u^2) (s/u)) :
    a+q+v*(H+D) ≤ (4/5)*(u+3*v)*(5*u-10*v) := by
  by_cases hz : u=0
  · have hzv : v=0 := by nlinarith
    have hzH : H=0 := by nlinarith
    have hzD : D=0 := by nlinarith
    have hza : a=0 := by nlinarith
    have hzq : q=0 := by nlinarith
    simp [hz,hzv,hzH,hzD,hza,hzq]
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
  have hcap := pointwise_energy_cap (hnorm hup)
  have hscaled := mul_le_mul_of_nonneg_left hcap (sq_nonneg u)
  have hi : u^2*W (v/u) (H/u) (D/u) (a/u^2) (q/u^2)=a+q+v*(H+D) := by
    unfold W
    field_simp <;> ring
  have hi' : u^2*B0 (v/u)=(4/5)*(u+3*v)*(5*u-10*v) := by
    unfold B0
    field_simp <;> ring
  rwa [hi,hi'] at hscaled

/-- The full n>=20 retained square, with its NONNEGATIVE common loss. -/
theorem concentrated_ge100 (N j r H D a q s : ℝ) (hN : 100 ≤ N)
    (h : Hyp r H D a q s) :
    energy N j r H D a q + (N-100)*(1+3*r)*(5-10*r)/125 ≤
      (25/(24*N))*(mass N j r H D)^2 := by
  have hn0 : 0 < N := by linarith
  have hid : (25/(24*N))*(mass N j r H D)^2-energy N j r H D a q =
      (25/(24*N))*(mass N j r H D-12*N*(2+r)/25)^2+
      (N/125)*(1+3*r)*(5-10*r)-W r H D a q := by
    unfold energy mass W
    field_simp
    ring
  have hs := mul_nonneg (show 0 ≤ 25/(24*N) by positivity)
    (sq_nonneg (mass N j r H D-12*N*(2+r)/25))
  have hc := pointwise_energy_cap h
  dsimp [B0] at hc
  nlinarith only [hid,hs,hc]

theorem common_loss_nonnegative (N r : ℝ) (hN : 100 ≤ N)
    (hr : 0 ≤ r) (hr' : r ≤ 1/2) :
    0 ≤ (N-100)*(1+3*r)*(5-10*r)/125 := by
  exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith))
    (by linarith)) (by norm_num)
end
end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
