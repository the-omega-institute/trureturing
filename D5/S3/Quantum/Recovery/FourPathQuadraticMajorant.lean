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

/-! The complementary real and imaginary phase deficits control the four-path response. -/
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false

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
      281/200 < r ∧ r < 10/7 ∧ r^2=2 := by
  dsimp
  have r0 := Real.sqrt_nonneg (2 : ℝ)
  have r2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have rl : (281/200:ℝ) < Real.sqrt 2 := by nlinarith
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
  have hprod : (u^2-v^2)^2 = 4-4*(u*v)^2 := by
    calc
      _ = (u^2+v^2)^2-4*(u*v)^2 := by ring
      _ = _ := by rw [hs]; ring
  have hsq : (u+v)^2 ≤ 4-(u^2-v^2)^2/4 := by
    nlinarith [sq_nonneg (1-u*v)]
  have hd : 0 ≤ (u^2-v^2)^2 ∧ (u^2-v^2)^2 ≤ 4 := by
    constructor
    · positivity
    · nlinarith [sq_nonneg (u*v)]
  have hr : 0 ≤ 2-(u^2-v^2)^2/16 := by linarith
  have ht : 4-(u^2-v^2)^2/4 ≤ (2-(u^2-v^2)^2/16)^2 := by
    nlinarith [sq_nonneg ((u^2-v^2)^2)]
  exact (sq_le_sq₀ (by positivity : 0 ≤ u+v) hr).mp (hsq.trans ht)

private lemma scaled_pair_deficit (u v a t : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : 0 < a) (hu2 : u^2=a^2+t) (hv2 : v^2=a^2-t) :
    u+v ≤ 2*a-t^2/(4*a^3) := by
  have hh := pair_deficit (u/a) (v/a) (div_nonneg hu ha.le) (div_nonneg hv ha.le)
    (by field_simp [ne_of_gt ha]; nlinarith)
  have hd : (u/a)^2-(v/a)^2 = 2*t/a^2 := by
    field_simp [ne_of_gt ha]
    nlinarith
  rw [hd] at hh
  have h := (mul_le_mul_iff_right₀ ha).mpr hh
  field_simp [ne_of_gt ha] at h ⊢
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
  change 281/200 < r at rl
  change r < 10/7 at ru
  change r^2=2 at r2
  have rp : 0 < r := by linarith
  have cp : 0 < c := lt_of_lt_of_le sp sc
  have asq : a^2=c^2*p+s^2*q := by
    rw [ha, Real.sq_sqrt (by positivity)]
  have an : 0 ≤ a := ha ▸ Real.sqrt_nonneg _
  have sa : s ≤ a := by
    have h := mul_nonneg hp (show 0 ≤ c^2-s^2 by nlinarith)
    nlinarith
  have ac : a ≤ c := by
    have h := mul_nonneg hq (show 0 ≤ c^2-s^2 by nlinarith)
    nlinarith
  have ap : 0 < a := lt_of_lt_of_le sp sa
  change m=c*p+s*q at hm
  have sm : s ≤ m := by nlinarith [mul_nonneg hp (sub_nonneg.mpr sc)]
  have mp : 0 < m := lt_of_lt_of_le sp sm
  have am : a^2-m^2=(c-s)^2*p*q := by
    calc
      _ = (c^2*p+s^2*q)*(p+q)-(c*p+s*q)^2 := by rw [hpq,hm,asq]; ring
      _ = _ := by ring
  have ma : m ≤ a := by nlinarith [mul_nonneg (sq_nonneg (c-s)) (mul_nonneg hp hq)]
  have mid : m*(c+s)=a^2+c*s := by
    calc
      _ = c^2*p+s^2*q+c*s*(p+q) := by rw [hm]; ring
      _ = _ := by rw [hpq,asq]; ring
  have mn : 9/10*a ≤ m := by
    have hg : 0 < c*s-(81/400)*(c+s)^2 := by nlinarith only [cs1,cs,rl]
    have hsquare := sq_nonneg (a-(9/20)*(c+s))
    have hpos : 0 ≤ (c+s)*(m-9/10*a) := by nlinarith only [mid,hsquare,hg]
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hpos (by positivity : 0 < c+s))
  have Ln : 0 ≤ L := hL ▸ Real.sqrt_nonneg _
  have Lsq : L^2=2+4*a^2+4*r*m := by
    rw [hL, Real.sq_sqrt (by positivity)]
  have am0 : 0 ≤ a^2-m^2 := by rw [am]; positivity
  have Ll : r+2*m ≤ L := by nlinarith only [Lsq,r2,am0,Ln,rp,mp]
  have Lu : L ≤ r+2*a := by
    have h := mul_le_mul_of_nonneg_left ma (show 0 ≤ 4*r by positivity)
    nlinarith only [Lsq,r2,h,Ln,rp,an]
  let N := (a+m)*(r+2*a+L)
  have Np : 0 < N := by dsimp [N]; positivity
  have identity : (r+2*a-L)*N=4*r*(c-s)^2*p*q := by
    have hi : (r+2*a)^2-L^2=4*r*(a-m) := by nlinarith only [Lsq,r2]
    calc
      _ = ((r+2*a)^2-L^2)*(a+m) := by dsimp [N]; ring
      _ = 4*r*(a^2-m^2) := by rw [hi]; ring
      _ = _ := by rw [am]; ring
  have N1 : 8*(c-s)^2 ≤ N := by
    have h1 : 4*r*s+8*s^2 ≤ N := by
      have h := mul_le_mul (show 2*s ≤ a+m by linarith)
        (show 2*r+4*s ≤ r+2*a+L by linarith) (by positivity) (by positivity)
      dsimp [N] at h ⊢
      nlinarith only [h]
    have sr : 2*s ≤ r := by nlinarith only [cs1,sc,sp,rp,r2,ds']
    have h := mul_nonneg sp.le (show 0 ≤ r-2*s by linarith)
    nlinarith only [h1,h,ds]
  have N2base : 19/5*r*a+361/50*a^2 ≤ N := by
    have h1 := mul_nonneg (show 0 ≤ a+m by positivity) (show 0 ≤ L-r-2*m by linarith)
    have h2 := mul_nonneg (show 0 ≤ a+m-19/10*a by linarith)
      (show 0 ≤ 2*r+2*(a+m)+19/5*a by positivity)
    dsimp [N]
    nlinarith only [h1,h2]
  have F : 0 ≤ 19/5*r+361/50*a-32*(r-1)*a^2 := by
    have r1 : 0 ≤ r-1 := by linarith only [rl]
    have hchord := mul_nonneg (show 0 ≤ (r-1)*a by positivity)
      (show 0 ≤ 15/16-a by linarith)
    have hend : 0 ≤ (5583-3892*r)/160 := by linarith
    have hblend := mul_nonneg (show 0 ≤ a by positivity) hend
    have hleft := mul_nonneg (show 0 ≤ 15/16-a by linarith) (show 0 ≤ 19/5*r by positivity)
    nlinarith only [hchord, hblend, hleft]
  have N2 : 32*r*(c-s)^2*a^3 ≤ N := by
    have h := mul_nonneg ap.le F
    have heq : r*(c-s)^2=r-1 := by
      rw [ds']; nlinarith only [r2]
    have heq' : 32*r*(c-s)^2*a^3=32*(r-1)*a^3 := by rw [show 32*r*(c-s)^2=32*(r*(c-s)^2) by ring,heq]
    rw [heq']
    nlinarith only [h,N2base]
  have dpos : 0 < (c-s)^2 := by rw [ds]; positivity
  constructor
  · apply (le_div_iff₀ rp).mpr
    have h := mul_le_mul_of_nonneg_left N1 (show 0 ≤ r+2*a-L by linarith)
    have idr : ((r+2*a-L)*N)*r=8*(c-s)^2*p*q := by
      rw [identity]
      calc
        _ = 4*r^2*(c-s)^2*p*q := by ring
        _ = _ := by rw [r2]; ring
    have hh := mul_le_mul_of_nonneg_right h rp.le
    rw [idr] at hh
    have hh' : ((r+2*a-L)*r)*(8*(c-s)^2) ≤ (p*q)*(8*(c-s)^2) := by
      nlinarith only [hh]
    exact (mul_le_mul_iff_left₀ (show 0 < 8*(c-s)^2 by positivity)).mp hh'
  · apply (le_div_iff₀ (show 0 < 8*a^3 by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left N2 (show 0 ≤ r+2*a-L by linarith only [Lu])
    have hh : ((r+2*a-L)*(8*a^3))*(4*r*(c-s)^2) ≤ (p*q)*(4*r*(c-s)^2) := by
      nlinarith only [identity,h]
    exact (mul_le_mul_iff_left₀ (show 0 < 4*r*(c-s)^2 by positivity)).mp hh



private lemma normalized_majorant (xi eta : ℂ) (hn : ‖xi‖^2+‖eta‖^2=1) :
    ((‖xi+eta‖+‖xi-eta‖)/Real.sqrt 2 +
      ‖(Real.cos (Real.pi/8):ℂ)*xi+Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖+
      ‖(Real.cos (Real.pi/8):ℂ)*xi-Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖)^2 ≤
    (Real.sqrt 2+2*Real.cos (Real.pi/8))^2*‖xi‖^2+
      (Real.sqrt 2+2*Real.sin (Real.pi/8))^2*‖eta‖^2 := by
  let r := Real.sqrt 2
  let c := Real.cos (Real.pi/8)
  let s := Real.sin (Real.pi/8)
  let p := ‖xi‖^2
  let q := ‖eta‖^2
  let x := (xi*star eta).re
  let y := (xi*star eta).im
  let a := Real.sqrt (c^2*p+s^2*q)
  let m := c*p+s*q
  let L := Real.sqrt (2+4*a^2+4*r*m)
  have hp : 0 ≤ p := sq_nonneg _
  have hq : 0 ≤ q := sq_nonneg _
  have hnorm (z : ℂ) : ‖z‖^2=z.re^2+z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have phase : x^2+y^2=p*q := by
    simp [x,y,p,q,hnorm,Complex.mul_re,Complex.mul_im,Complex.star_def]
    ring
  have asq : a^2=c^2*p+s^2*q := Real.sq_sqrt (by positivity)
  obtain ⟨sp, sc, cu, cs1, cs, ds, ds', rl, ru, r2⟩ := constants
  change 0 < s at sp
  change s ≤ c at sc
  change c*s=r/4 at cs
  change r^2=2 at r2
  have rp : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have cp : 0 < c := lt_of_lt_of_le sp sc
  have mp : 0 ≤ m := by dsimp [m]; positivity
  have ap : 0 < a := by
    have csq : 0 < c^2 := sq_pos_of_pos (lt_of_lt_of_le sp sc)
    have ssq : 0 < s^2 := sq_pos_of_pos sp
    have hs : 0 < c^2*p+s^2*q := by
      by_cases pp : p=0
      · have qq : q=1 := by change p+q=1 at hn; linarith
        rw [pp,qq]; nlinarith
      · exact add_pos_of_pos_of_nonneg (mul_pos csq (lt_of_le_of_ne hp (Ne.symm pp))) (by positivity)
    exact Real.sqrt_pos.mpr hs
  have normplus : ‖xi+eta‖^2=1+2*x := by
    rw [hnorm]
    simp [x,Complex.mul_re,Complex.star_def,hnorm] at hn ⊢
    nlinarith
  have normminus : ‖xi-eta‖^2=1-2*x := by
    rw [hnorm]
    simp [x,Complex.mul_re,Complex.star_def,hnorm] at hn ⊢
    nlinarith
  have hA := scaled_pair_deficit ‖xi+eta‖ ‖xi-eta‖ 1 (2*x)
    (norm_nonneg _) (norm_nonneg _) (by norm_num) (by nlinarith [normplus]) (by nlinarith [normminus])
  have A : (‖xi+eta‖+‖xi-eta‖)/r ≤ r-x^2/r := by
    apply (div_le_iff₀ rp).mpr
    have rr : (r-x^2/r)*r=2-x^2 := by field_simp; nlinarith [r2]
    rw [rr]
    nlinarith [hA]
  let u := ‖(c:ℂ)*xi+Complex.I*(s:ℂ)*eta‖
  let v := ‖(c:ℂ)*xi-Complex.I*(s:ℂ)*eta‖
  have u2 : u^2=a^2+2*c*s*y := by
    dsimp [u]
    rw [hnorm,asq]
    simp [p,q,y,hnorm,Complex.star_def,Complex.mul_im,Complex.mul_re]
    ring
  have v2 : v^2=a^2-2*c*s*y := by
    dsimp [v]
    rw [hnorm,asq]
    simp [p,q,y,hnorm,Complex.star_def,Complex.mul_im,Complex.mul_re]
    ring
  have hB := scaled_pair_deficit u v a (2*c*s*y) (norm_nonneg _) (norm_nonneg _) ap u2 v2
  have cs2 : (c*s)^2=1/8 := by rw [cs]; nlinarith [r2]
  have B : u+v ≤ 2*a-y^2/(8*a^3) := by
    have heq : (2*c*s*y)^2/(4*a^3)=y^2/(8*a^3) := by
      field_simp
      nlinarith only [cs2]
    rwa [heq] at hB
  obtain ⟨g1,g2⟩ := radius_gap p q a m L hp hq hn rfl rfl rfl
  change r+2*a-L ≤ p*q/r at g1
  change r+2*a-L ≤ p*q/(8*a^3) at g2
  have gap : r+2*a-L ≤ x^2/r+y^2/(8*a^3) := by
    by_cases hc : 8*a^3 ≤ r
    · have hh := div_le_div_of_nonneg_left (sq_nonneg y) (show 0 < 8*a^3 by positivity) hc
      rw [← phase,add_div] at g1
      linarith
    · have hh := div_le_div_of_nonneg_left (sq_nonneg x) rp (le_of_lt (lt_of_not_ge hc))
      rw [← phase,add_div] at g2
      linarith
  have total : (‖xi+eta‖+‖xi-eta‖)/r+u+v ≤ L := by linarith
  have Lsq : L^2=(r+2*c)^2*p+(r+2*s)^2*q := by
    have sq : L^2=2+4*a^2+4*r*m := Real.sq_sqrt (by positivity)
    change p+q=1 at hn
    calc
      _ = 2*(p+q)+4*(c^2*p+s^2*q)+4*r*(c*p+s*q) := by rw [hn,← asq]; simpa only [mul_one] using sq
      _ = (r^2+4*r*c+4*c^2)*p+(r^2+4*r*s+4*s^2)*q := by rw [r2]; ring
      _ = _ := by ring
  have nonneg : 0 ≤ (‖xi+eta‖+‖xi-eta‖)/r+u+v := by dsimp [u,v]; positivity
  change ((‖xi+eta‖+‖xi-eta‖)/r+u+v)^2 ≤ (r+2*c)^2*p+(r+2*s)^2*q
  rw [← Lsq]
  exact (sq_le_sq₀ nonneg (Real.sqrt_nonneg _)).mpr total

/-- The four-path majorant for every complex pair, without normalization. -/
theorem four_path_quadratic_majorant (xi eta : ℂ) :
    ((‖xi+eta‖+‖xi-eta‖)/Real.sqrt 2 +
      ‖(Real.cos (Real.pi/8):ℂ)*xi+Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖+
      ‖(Real.cos (Real.pi/8):ℂ)*xi-Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖)^2 ≤
    (Real.sqrt 2+2*Real.cos (Real.pi/8))^2*‖xi‖^2+
      (Real.sqrt 2+2*Real.sin (Real.pi/8))^2*‖eta‖^2 := by
  let t := Real.sqrt (‖xi‖^2+‖eta‖^2)
  have tsq : t^2=‖xi‖^2+‖eta‖^2 := Real.sq_sqrt (by positivity)
  by_cases ht : t=0
  · have xz : xi=0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖eta‖,norm_nonneg xi])
    have yz : eta=0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖xi‖,norm_nonneg eta])
    simp [xz,yz]
  · have tp : 0 < t := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm ht)
    have tc : (t:ℂ) ≠ 0 := by exact_mod_cast ht
    have normdiv (z : ℂ) : ‖z/(t:ℂ)‖=‖z‖/t := by rw [norm_div,Complex.norm_of_nonneg tp.le]
    have hn : ‖xi/(t:ℂ)‖^2+‖eta/(t:ℂ)‖^2=1 := by
      rw [normdiv,normdiv]
      field_simp
      nlinarith [tsq]
    have h := normalized_majorant (xi/(t:ℂ)) (eta/(t:ℂ)) hn
    have plus : xi/(t:ℂ)+eta/(t:ℂ)=(xi+eta)/(t:ℂ) := by ring
    have minus : xi/(t:ℂ)-eta/(t:ℂ)=(xi-eta)/(t:ℂ) := by ring
    have plus' : (Real.cos (Real.pi/8):ℂ)*(xi/(t:ℂ))+Complex.I*(Real.sin (Real.pi/8):ℂ)*(eta/(t:ℂ)) =
        ((Real.cos (Real.pi/8):ℂ)*xi+Complex.I*(Real.sin (Real.pi/8):ℂ)*eta)/(t:ℂ) := by ring
    have minus' : (Real.cos (Real.pi/8):ℂ)*(xi/(t:ℂ))-Complex.I*(Real.sin (Real.pi/8):ℂ)*(eta/(t:ℂ)) =
        ((Real.cos (Real.pi/8):ℂ)*xi-Complex.I*(Real.sin (Real.pi/8):ℂ)*eta)/(t:ℂ) := by ring
    rw [plus,minus,plus',minus'] at h
    simp only [normdiv] at h
    have h' :
        (((‖xi+eta‖+‖xi-eta‖)/Real.sqrt 2 +
          ‖(Real.cos (Real.pi/8):ℂ)*xi+Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖+
          ‖(Real.cos (Real.pi/8):ℂ)*xi-Complex.I*(Real.sin (Real.pi/8):ℂ)*eta‖)^2)/t^2 ≤
        ((Real.sqrt 2+2*Real.cos (Real.pi/8))^2*‖xi‖^2+
          (Real.sqrt 2+2*Real.sin (Real.pi/8))^2*‖eta‖^2)/t^2 := by
      convert h using 1 <;> field_simp [ht]
    exact (div_le_div_iff_of_pos_right (sq_pos_of_pos tp)).mp h'

end D5.S3.Quantum.Recovery.FourPathQuadraticMajorant
