/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfStep
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:consumed-half-step-interpolation)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Half-step chart interpolation, complete residues and native dyadic masks. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.HalfK4Certificates
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.HalfF4Certificates
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.HalfBothCertificates

/-! SOURCE_ONLY_UNCOMPILED. The three charts cover dyadic KF>=4; they
are not a claim that every real K,F with KF>=4 lies in one of the charts. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining
open private rectangle scaled_margin grain_q half_margin scaled_to_rectangle
  ArithmeticSelection NativeChoice native_of_selection dyadic_time_cases from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.Arithmetic
open private half_power from D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint
open private half_K4_negative half_K4_p11 half_K4_p1r half_K4_ph1 half_K4_phr
  half_K4_boundary from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.HalfK4Certificates
open private half_F4_negative half_F4_p11 half_F4_p1r half_F4_ph1 half_F4_phr
  half_F4_boundary from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.HalfF4Certificates
open private half_both2_negative half_both2_p11 half_both2_p1r half_both2_ph1
  half_both2_phr half_both2_boundary from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.HalfBothCertificates

private structure HalfCorners (K F e T : ℤ) : Prop where
  negative : ∀ i, 0≤half_margin K F e (8*K*F+T) 0 e i
  lo_lo : ∀ i, 0≤half_margin K F e (8*K*F+T) 1 1 i
  lo_hi : ∀ i, 0≤half_margin K F e (8*K*F+T) 1 (2*F*e) i
  hi_lo : ∀ i, 0≤half_margin K F e (8*K*F+T) (2*K) 1 i
  hi_hi : ∀ i, 0≤half_margin K F e (8*K*F+T) (2*K) (2*F*e) i
  boundary : ∀ i, 0≤rectangle (4*K*F) (2*K*F)
    (4*K*(F*e)*(4*K*F)) (2*K*(4*K*F)) (4*K*(F*e))
    (grain_q K (F*e) (4*K*F)) (2*F*e-e) 1 1 i

private theorem half_corners (K F e T : ℤ)
    (hK : 1≤K) (hF : 1≤F) (he : 1≤e) (hT : 0≤T)
    (hregion : 4≤K ∨ 4≤F ∨ (2≤K ∧ 2≤F)) :
    HalfCorners K F e T := by
  rcases hregion with hK4|hF4|hboth
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro i
      convert half_K4_negative (K-4) (F-1) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_K4_p11 (K-4) (F-1) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_K4_p1r (K-4) (F-1) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_K4_ph1 (K-4) (F-1) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_K4_phr (K-4) (F-1) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_K4_boundary (K-4) (F-1) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro i
      convert half_F4_negative (K-1) (F-4) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_F4_p11 (K-1) (F-4) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_F4_p1r (K-1) (F-4) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_F4_ph1 (K-1) (F-4) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_F4_phr (K-1) (F-4) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_F4_boundary (K-1) (F-4) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro i
      convert half_both2_negative (K-2) (F-2) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_both2_p11 (K-2) (F-2) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_both2_p1r (K-2) (F-2) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_both2_ph1 (K-2) (F-2) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_both2_phr (K-2) (F-2) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring
    · intro i
      convert half_both2_boundary (K-2) (F-2) (e-1) T
        (by omega) (by omega) (by omega) hT i using 1 <;> congr 1 <;> ring

/-- Interpolation in r, then in h. The explicit identities prevent an
accidental assumption about a bilinear cross term. -/
private theorem half_interpolate (K F e T h r : ℤ)
    (hK : 1≤K) (hF : 1≤F) (he : 1≤e)
    (hh : 1≤h ∧ h≤2*K) (hr : 1≤r ∧ r≤2*F*e)
    (corners : HalfCorners K F e T) :
    ∀ i, 0≤half_margin K F e (8*K*F+T) h r i := by
  have hFe := mul_nonneg (show 0≤F-1 by omega) (show 0≤e-1 by omega)
  have hwidth : 0<2*F*e-1 := by nlinarith only [hFe,hF,he]
  intro i
  let f := fun h r => half_margin K F e (8*K*F+T) h r i
  have hlo : 0≤f 1 r := by
    have hid : (2*F*e-1)*f 1 r =
        (2*F*e-r)*f 1 1+(r-1)*f 1 (2*F*e) := by
      dsimp [f]
      fin_cases i <;> dsimp [half_margin,scaled_margin,grain_q] <;> ring
    have hn := add_nonneg
      (mul_nonneg (show 0≤2*F*e-r by omega) (corners.lo_lo i))
      (mul_nonneg (show 0≤r-1 by omega) (corners.lo_hi i))
    change 0≤(2*F*e-r)*f 1 1+(r-1)*f 1 (2*F*e) at hn
    rw [←hid] at hn
    exact nonneg_of_mul_nonneg_right hn hwidth
  have hhi : 0≤f (2*K) r := by
    have hid : (2*F*e-1)*f (2*K) r =
        (2*F*e-r)*f (2*K) 1+(r-1)*f (2*K) (2*F*e) := by
      dsimp [f]
      fin_cases i <;> dsimp [half_margin,scaled_margin,grain_q] <;> ring
    have hn := add_nonneg
      (mul_nonneg (show 0≤2*F*e-r by omega) (corners.hi_lo i))
      (mul_nonneg (show 0≤r-1 by omega) (corners.hi_hi i))
    change 0≤(2*F*e-r)*f (2*K) 1+(r-1)*f (2*K) (2*F*e) at hn
    rw [←hid] at hn
    exact nonneg_of_mul_nonneg_right hn hwidth
  have hid : (2*K-1)*f h r=(2*K-h)*f 1 r+(h-1)*f (2*K) r := by
    dsimp [f]
    fin_cases i <;> dsimp [half_margin,scaled_margin,grain_q] <;> ring
  have hn := add_nonneg (mul_nonneg (show 0≤2*K-h by omega) hlo)
    (mul_nonneg (show 0≤h-1 by omega) hhi)
  rw [←hid] at hn
  exact nonneg_of_mul_nonneg_right hn (by omega)


/-- The last +1 makes r positive even at exact multiples of 2J. -/
private theorem half_floor_split (K J e n : ℤ)
    (hK : 1≤K) (hJ : 1≤J) (he : 1≤e)
    (hn : 1≤n ∧ n≤4*K*J-e) :
    ∃ h r : ℤ, 1≤h ∧ h≤2*K ∧ 1≤r ∧ r≤2*J ∧ n=2*J*h-r := by
  let u := n/(2*J)
  let rem := n%(2*J)
  have hu : 0≤u := Int.ediv_nonneg (by omega) (by omega)
  have hrem0 : 0≤rem := Int.emod_nonneg _ (by omega)
  have hrem1 : rem<2*J := Int.emod_lt_of_pos _ (by omega)
  have hdiv : rem+2*J*u=n := by
    simpa only [u,rem] using Int.emod_add_ediv n (2*J)
  have hu1 : u<2*K := by
    by_contra hh
    have hp := mul_nonneg (show 0≤2*J by omega) (show 0≤u-2*K by omega)
    nlinarith only [hp,hdiv,hrem0,hn.2,he]
  refine ⟨u+1,2*J-rem,by omega,by omega,by omega,by omega,?_⟩
  nlinarith only [hdiv]

private theorem half_arithmetic (K F e t : ℤ)
    (hK : 1≤K) (hF : 1≤F) (he : 1≤e) (hz : 8≤2*K*F)
    (hregion : 4≤K ∨ 4≤F ∨ (2≤K ∧ 2≤F))
    (ht : t=4*K*F ∨ 8*K*F≤t) (heven : t%2=0) :
    Nonempty (ArithmeticSelection t (2*K*F) K (F*e)) := by
  have hK0 : 0<K := by omega
  have hF0 : 0<F := by omega
  have he0 : 0<e := by omega
  have hFe := mul_nonneg (show 0≤F-1 by omega) (show 0≤e-1 by omega)
  have hJ : 1≤F*e := by nlinarith only [hFe,hF,he]
  rcases ht with ht|ht
  · subst t
    have cert := half_corners K F e 0 hK hF he (by omega) hregion
    refine ⟨⟨2*F*e-e,1,1,⟨?_,?_⟩,⟨by norm_num,?_⟩,
      ⟨by norm_num,by nlinarith⟩,?_⟩⟩
    · have hp := mul_nonneg (show 0≤F-1 by omega) (show 0≤e by omega)
      nlinarith only [hp,he]
    · have hp := mul_nonneg (show 0≤4*K-2 by omega) (show 0≤F*e by positivity)
      nlinarith only [hp,he]
    · have hp := mul_pos (show 0<2*K*F by nlinarith) (show 0<4*K-2 by omega)
      nlinarith only [hp]
    · simpa only [mul_assoc] using cert.boundary
  · let z := 2*K*F
    let m := t/2
    let k := (-m)%(z+1)-1
    let v := -((-m)/(z+1))
    let n := e*(2*k+1)
    have hz0 : 8≤z := hz
    have ht0 : 4*z≤t := by dsimp [z]; nlinarith only [ht]
    have hm : t=2*m := by dsimp [m]; omega
    have hmz : 2*z≤m := by omega
    have hk0 : -1≤k := by
      have := Int.emod_nonneg (-m) (show z+1≠0 by omega)
      dsimp [k]
      omega
    have hk1 : k≤z-1 := by
      have := Int.emod_lt_of_pos (-m) (show 0<z+1 by omega)
      dsimp [k]
      omega
    have hv : (z+1)*v=m+k+1 := by
      have hh := Int.emod_add_ediv (-m) (z+1)
      dsimp [k,v]
      nlinarith only [hh]
    have hv0 : 0≤v := by
      by_contra hh
      have hp := mul_neg_of_pos_of_neg (show 0<z+1 by omega) (show v<0 by omega)
      nlinarith only [hp,hv,hmz,hk0,hz0]
    have hv1 : 2*v≤t-2 := by
      by_contra hh
      have hvv : m≤v := by omega
      have hp := mul_le_mul_of_nonneg_left hvv (show 0≤z+1 by omega)
      have hprod := mul_nonneg (show 0≤z-1 by omega) (show 0≤m-2 by omega)
      nlinarith only [hp,hprod,hv,hk1,hmz,hz0]
    have cert := half_corners K F e (t-8*K*F) hK hF he (by omega) hregion
    have make (h r : ℤ) (hh : 0≤h ∧ h≤2*K)
        (hr : 1≤r ∧ r≤4*K*(F*e)) (hn : n=2*(F*e)*h-r)
        (hmarg : ∀ i, 0≤half_margin K F e t h r i) :
        Nonempty (ArithmeticSelection t (2*K*F) K (F*e)) := by
      refine ⟨⟨r,h,v,hr,⟨hh.1,?_⟩,⟨hv0,hv1⟩,?_⟩⟩
      · have hp := mul_nonneg (show 0≤2*z by omega) (show 0≤2*K-h by omega)
        have hp' := mul_pos (show 0<2*K by omega) (show 0<t-2*z by omega)
        change 2*z*h<2*K*t
        nlinarith only [hp,hp']
      · apply scaled_to_rectangle _ _ _ _ _ _ _ _ e
          (e*(t+2*K*F-1)+(2*(F*e)*h-r)) (e*(2*K*F-2)) v
          (by omega) (by nlinarith only [hz])
        · have hv' := congrArg (fun u : ℤ => 2*e*u) hv
          dsimp [n] at hn
          dsimp [z] at hv'
          nlinarith only [hv',hn,hm]
        · exact hmarg
    by_cases hk : k=-1
    · have hn : n= -e := by dsimp [n]; rw [hk]; ring
      apply make 0 e ⟨by omega,by omega⟩ ⟨he,?_⟩ (by rw [hn]; ring)
      · have hp := mul_nonneg (show 0≤4*K*F-1 by nlinarith) (show 0≤e by omega)
        nlinarith only [hp]
      · intro i
        convert cert.negative i using 1 <;> congr 1 <;> ring
    · have hk2 : 0≤k := by omega
      have hn0 : 1≤n := by
        have hp := mul_nonneg (show 0≤e-1 by omega) (show 0≤2*k+1 by omega)
        dsimp [n]
        nlinarith only [hp,he,hk2]
      have hn1 : n≤4*K*(F*e)-e := by
        have hp := mul_nonneg (show 0≤e by omega) (show 0≤z-1-k by omega)
        dsimp [n]
        dsimp [z] at hp
        nlinarith only [hp]
      obtain ⟨h,r,hh0,hh1,hr0,hr1,hn⟩ := half_floor_split K (F*e) e n hK hJ he ⟨hn0,hn1⟩
      apply make h r ⟨by omega,hh1⟩ ⟨hr0,?_⟩ hn
      · have hp := mul_nonneg (show 0≤4*K-2 by omega) (show 0≤F*e by positivity)
        nlinarith only [hr1,hp]
      · intro i
        convert half_interpolate K F e (t-8*K*F) h r hK hF he
          ⟨hh0,hh1⟩ ⟨hr0,by nlinarith only [hr1]⟩ cert i using 1 <;> congr 1 <;> ring

/-- Consuming interface for c>=3, a>c+d, b<=c+d, with no grain bound. -/
private theorem half_step_choice_exists (a b c d : ℕ)
    (hc : 3≤c) (hcd : c<d) (hdb : d<b) (hba : b<a)
    (ha : c+d<a) (hb : b≤c+d) : Nonempty (NativeChoice a b c d) := by
  let K : ℤ := 2^(b-d-1)
  let F : ℤ := 2^(c+d-b)
  let e : ℤ := 2^(a-c-d-1)
  have hK : 1≤K := by dsimp [K]; exact one_le_pow₀ (by norm_num)
  have hF : 1≤F := by dsimp [F]; exact one_le_pow₀ (by norm_num)
  have he : 1≤e := by dsimp [e]; exact one_le_pow₀ (by norm_num)
  have hz : (2:ℤ)^c=2*K*F := by
    have hexp : c=(b-d-1)+(c+d-b)+1 := by omega
    conv_lhs => rw [hexp]
    dsimp [K,F]
    simp only [pow_add,pow_one]
    ring
  have hJ : (2:ℤ)^(a-b-1)=F*e := by
    dsimp [F,e]
    rw [←pow_add]
    congr 1
    omega
  have hz8 : (8:ℤ)≤2*K*F := by
    rw [←hz]
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hc
  have hregion : 4≤K ∨ 4≤F ∨ (2≤K ∧ 2≤F) := by
    by_cases h1 : 2≤b-d-1
    · left
      simpa [K] using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) h1
    by_cases h2 : 2≤c+d-b
    · right; left
      simpa [F] using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) h2
    · right; right
      have he1 : b-d-1=1 := by omega
      have he2 : c+d-b=1 := by omega
      simp [K,F,he1,he2]
  have ht : (2:ℤ)^d=4*K*F ∨ 8*K*F≤2^d := by
    rcases dyadic_time_cases c d hcd with h|h
    · left; rw [hz] at h; nlinarith only [h]
    · right; rw [hz] at h; nlinarith only [h]
  have ht2 : (2:ℤ)^d%2=0 := by rw [half_power d (by omega)]; omega
  obtain ⟨sel⟩ := half_arithmetic K F e (2^d) hK hF he hz8 hregion ht ht2
  refine ⟨native_of_selection a b c d (by omega) hcd hdb hba ?_⟩
  simpa only [K,hz,hJ] using sel

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining
