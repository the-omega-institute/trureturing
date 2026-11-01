/- GID: D5/S3/Quantum/Recovery/FourPathQuadraticMajorant
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathQuadraticMajorant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complementary phase deficits give the sharp weighted quadratic majorant for the four-path record. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Recovery.FourPathQuadraticMajorant
set_option autoImplicit false
set_option maxHeartbeats 1200000

private lemma constants :
    let r := Real.sqrt 2
    let c := Real.cos (Real.pi / 8)
    let s := Real.sin (Real.pi / 8)
    0 < s ∧ s ≤ c ∧ c < 15/16 ∧ c^2+s^2=1 ∧
      c*s=r/4 ∧ (c-s)^2=2*s^2 ∧ (c-s)^2=1-r/2 ∧
      7/5 < r ∧ r < 10/7 ∧ r^2=2 := by
  dsimp
  have r0 := Real.sqrt_nonneg (2 : ℝ)
  have r2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have rl : (7/5:ℝ) < Real.sqrt 2 := by nlinarith
  have ru : Real.sqrt 2 < (10/7:ℝ) := by nlinarith
  have cp := Real.cos_pos_of_mem_Ioo (show Real.pi/8 ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
    constructor <;> linarith [Real.pi_pos])
  have sp := Real.sin_pos_of_pos_of_lt_pi (by positivity : 0 < Real.pi/8)
    (by linarith [Real.pi_pos] : Real.pi/8 < Real.pi)
  have hcs := Real.sin_sq_add_cos_sq (Real.pi/8)
  have cc : Real.cos (Real.pi/8)^2 = (2+Real.sqrt 2)/4 := by
    rw [Real.cos_pi_div_eight]
    have h := Real.sq_sqrt (show 0 ≤ 2+Real.sqrt 2 by positivity)
    nlinarith
  have cs : Real.cos (Real.pi/8)*Real.sin (Real.pi/8) = Real.sqrt 2/4 := by
    have h := Real.sin_two_mul (Real.pi/8)
    rw [show 2*(Real.pi/8)=Real.pi/4 by ring, Real.sin_pi_div_four] at h
    nlinarith
  refine ⟨sp, ?_, ?_, by linarith, cs, ?_, ?_, rl, ru, r2⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- A paired nonnegative square-root response has a quartic phase deficit. -/
private lemma pair_deficit (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : u^2+v^2=2) :
    u+v ≤ 2-(u^2-v^2)^2/16 := by
  have huv : 0 ≤ u*v := mul_nonneg hu hv
  have huv1 : u*v ≤ 1 := by nlinarith [sq_nonneg (u-v)]
  have hprod : (u^2-v^2)^2 = 4-4*(u*v)^2 := by nlinarith [sq_nonneg (u^2+v^2-2)]
  have hsq : (u+v)^2 ≤ 4-(u^2-v^2)^2/4 := by
    nlinarith [sq_nonneg (1-u*v)]
  have hd : 0 ≤ (u^2-v^2)^2 ∧ (u^2-v^2)^2 ≤ 4 := by
    constructor
    · positivity
    · nlinarith [sq_nonneg (u*v)]
  have hr : 0 ≤ 2-(u^2-v^2)^2/16 := by linarith
  have ht : 4-(u^2-v^2)^2/4 ≤ (2-(u^2-v^2)^2/16)^2 := by
    nlinarith [sq_nonneg ((u^2-v^2)^2)]
  nlinarith [sq_nonneg (u+v-(2-(u^2-v^2)^2/16))]

private lemma scaled_pair_deficit (u v a t : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : 0 < a) (hu2 : u^2=a^2+t) (hv2 : v^2=a^2-t) :
    u+v ≤ 2*a-t^2/(4*a^3) := by
  have hh := pair_deficit (u/a) (v/a) (div_nonneg hu ha.le) (div_nonneg hv ha.le)
    (by field_simp; nlinarith)
  have hd : (u/a)^2-(v/a)^2 = 2*t/a^2 := by
    field_simp
    nlinarith
  rw [hd] at hh
  have h := (mul_le_mul_iff_right₀ ha).mpr hh
  field_simp at h ⊢
  nlinarith

/-- The two complementary deficits pay the weighted-radius gap. -/
private lemma radius_gap (p q a m L : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p+q=1)
    (ha : a=Real.sqrt ((Real.cos (Real.pi/8))^2*p+(Real.sin (Real.pi/8))^2*q))
    (hm : m=Real.cos (Real.pi/8)*p+Real.sin (Real.pi/8)*q)
    (hL : L=Real.sqrt (2+4*a^2+4*Real.sqrt 2*m)) :
    Real.sqrt 2+2*a-L ≤ p*q/Real.sqrt 2 ∧
      Real.sqrt 2+2*a-L ≤ p*q/(8*a^3) := by
  let r := Real.sqrt 2
  let c := Real.cos (Real.pi/8)
  let s := Real.sin (Real.pi/8)
  obtain ⟨sp, sc, cu, cs1, cs, ds, ds', rl, ru, r2⟩ := constants
  change 0 < s at sp
  change s ≤ c at sc
  change c < 15/16 at cu
  change c^2+s^2=1 at cs1
  change c*s=r/4 at cs
  change (c-s)^2=2*s^2 at ds
  change (c-s)^2=1-r/2 at ds'
  change 7/5 < r at rl
  change r < 10/7 at ru
  change r^2=2 at r2
  have rp : 0 < r := by linarith
  have cp : 0 < c := lt_of_lt_of_le sp sc
  have asq : a^2=c^2*p+s^2*q := by
    rw [ha, Real.sq_sqrt (by positivity)]
  have an : 0 ≤ a := ha ▸ Real.sqrt_nonneg _
  have sa : s ≤ a := by nlinarith [mul_nonneg hp (sub_nonneg.mpr sc)]
  have ac : a ≤ c := by
    have h := mul_nonneg hq (show 0 ≤ c^2-s^2 by nlinarith)
    nlinarith
  have ap : 0 < a := lt_of_lt_of_le sp sa
  change m=c*p+s*q at hm
  have sm : s ≤ m := by nlinarith [mul_nonneg hp (sub_nonneg.mpr sc)]
  have mp : 0 < m := lt_of_lt_of_le sp sm
  have am : a^2-m^2=(c-s)^2*p*q := by rw [hm]; nlinarith [hpq]
  have ma : m ≤ a := by nlinarith [mul_nonneg (sq_nonneg (c-s)) (mul_nonneg hp hq)]
  have mid : m*(c+s)=a^2+c*s := by rw [hm]; nlinarith
  have mn : 9/10*a ≤ m := by
    have hg : 0 < c*s-(81/400)*(c+s)^2 := by nlinarith
    have hsquare := sq_nonneg (a-(9/20)*(c+s))
    have hpos : 0 ≤ (c+s)*(m-9/10*a) := by nlinarith
    exact nonneg_of_mul_nonneg_left hpos (by positivity : 0 < c+s)
  have Ln : 0 ≤ L := hL ▸ Real.sqrt_nonneg _
  have Lsq : L^2=2+4*a^2+4*r*m := by
    rw [hL, Real.sq_sqrt (by positivity)]
  have Ll : r+2*m ≤ L := by nlinarith
  have Lu : L ≤ r+2*a := by nlinarith
  let N := (a+m)*(r+2*a+L)
  have Np : 0 < N := by dsimp [N]; positivity
  have identity : (r+2*a-L)*N=4*r*(c-s)^2*p*q := by
    dsimp [N]
    nlinarith [am, Lsq]
  have N1 : 8*(c-s)^2 ≤ N := by
    have h1 : 4*r*s+8*s^2 ≤ N := by
      have h := mul_le_mul (show 2*s ≤ a+m by linarith)
        (show 2*r+4*s ≤ r+2*a+L by linarith) (by positivity) (by positivity)
      dsimp [N]
      nlinarith
    have sr : 2*s ≤ r := by nlinarith
    have h := mul_nonneg sp.le (show 0 ≤ r-2*s by linarith)
    nlinarith
  have N2base : 19/5*r*a+361/50*a^2 ≤ N := by
    have h1 := mul_nonneg (show 0 ≤ a+m by positivity) (show 0 ≤ L-r-2*m by linarith)
    have h2 := mul_nonneg (show 0 ≤ a+m-19/10*a by linarith)
      (show 0 ≤ 2*r+2*(a+m)+19/5*a by positivity)
    dsimp [N]
    nlinarith
  have F : 0 ≤ 19/5*r+361/50*a-32*(r-1)*a^2 := by
    have hchord := mul_nonneg (show 0 ≤ (r-1)*a by positivity)
      (show 0 ≤ 15/16-a by linarith)
    have hend : 0 ≤ (5583-3892*r)/160 := by linarith
    have hblend := mul_nonneg (show 0 ≤ a by positivity) hend
    have hleft := mul_nonneg (show 0 ≤ 15/16-a by linarith) (show 0 ≤ 19/5*r by positivity)
    nlinarith only [hchord, hblend, hleft]
  have N2 : 32*r*(c-s)^2*a^3 ≤ N := by
    have h := mul_nonneg ap.le F
    have heq : r*(c-s)^2=r-1 := by nlinarith [ds']
    rw [show 32*r*(c-s)^2*a^3=32*(r-1)*a^3 by rw [← mul_assoc, heq]]
    nlinarith
  constructor
  · apply (le_div_iff₀ rp).mpr
    have h := mul_le_mul_of_nonneg_left N1 (show 0 ≤ r+2*a-L by linarith)
    have eq : 8*(c-s)^2 = 4*r*(c-s)^2*r := by nlinarith [r2]
    have h' : (r+2*a-L)*r ≤ p*q := by
      have dpos : 0 < (c-s)^2 := by rw [ds]; positivity
      nlinarith [identity, h, r2]
    exact h'
  · apply (le_div_iff₀ (show 0 < 8*a^3 by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left N2 (show 0 ≤ r+2*a-L by linarith)
    have dpos : 0 < r*(c-s)^2 := by rw [ds]; positivity
    nlinarith [identity]

end D5.S3.Quantum.Recovery.FourPathQuadraticMajorant
