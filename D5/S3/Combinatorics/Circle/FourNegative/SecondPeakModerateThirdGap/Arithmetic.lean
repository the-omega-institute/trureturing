/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakModerateThirdGap/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-moderate-third-gap-construction)
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: integer selector for the moderate-c third-gap sector; all floors are
   taken before the natural mask conversion. -/
import Mathlib.Data.Int.DivMod
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap
open SourceWidth PeriodicShortening RunFirstEarTransport

private def x (a : ℕ) : ℤ := 2^a
private def y (b : ℕ) : ℤ := 2^b
private def z (c : ℕ) : ℤ := 2^c
private def t (d : ℕ) : ℤ := 2^d
private def R (a d : ℕ) : ℤ := 2^(d-a-1)
private def r (c d : ℕ) : ℤ := 2^(c-d)
private def lam (b c : ℕ) : ℤ := 2^(b-c-1)

private def A (x y z : ℤ) : ℤ := 1+x+x*y+x*y*z
private def B (x y t : ℤ) : ℤ := 1+t+x*t+x*y*t
private def L (x z t : ℤ) : ℤ := 1+z+z*t+x*z*t
private def K (y z t : ℤ) : ℤ := 1+y+y*z+y*z*t
private def D (y z : ℤ) : ℤ := 1+y+y*z
private def N (x y z t : ℤ) : ℤ := x*y*z*t-1
private def C (x z t lam : ℤ) : ℤ := 2*lam*L x z t
private def E (x y z t : ℤ) : ℤ := N x y z t + A x y z - B x y t - K y z t

private def hm (E A C u : ℤ) : ℤ := (E+2*u*A)/C+1
private def hp (E A C u : ℤ) : ℤ := (E+2*u*A+A-1)/C
private def sAt (E A C u H : ℤ) : ℤ := C*H-E-2*u*A
private def ZAt (z lam H : ℤ) : ℤ := 1+lam*(z+H)*(z+1)
private def FAt (E A C z lam u H : ℤ) : ℤ :=
  sAt E A C u H-ZAt z lam H

/-- Euclidean division is used over integers, before any conversion to masks. -/
private theorem hm_bounds (e aa cc u : ℤ) (hc : 0<cc) :
    0<sAt e aa cc u (hm e aa cc u) ∧
      sAt e aa cc u (hm e aa cc u)≤cc := by
  have hd := Int.emod_add_mul_ediv (e+2*u*aa) cc
  have h0 := Int.emod_nonneg (e+2*u*aa) (ne_of_gt hc)
  have h1 := Int.emod_lt_of_pos (e+2*u*aa) hc
  dsimp [sAt,hm]
  constructor <;> nlinarith only [hd,h0,h1]

private theorem interval_iff (e aa cc u h : ℤ) (hc : 0<cc) :
    (hm e aa cc u≤h ↔ 0<sAt e aa cc u h) ∧
      (h≤hp e aa cc u ↔ sAt e aa cc u h≤aa-1) := by
  constructor
  · dsimp [hm,sAt]
    have hd := Int.ediv_lt_iff_lt_mul (a:=e+2*u*aa) (b:=h) hc
    rw [mul_comm cc h]
    omega
  · dsimp [hp,sAt]
    rw [Int.le_ediv_iff_mul_le hc]
    constructor <;> intro h <;> nlinarith only [h]

private theorem width_iff (e aa cc u g : ℤ) (hc : 0<cc) :
    g≤hp e aa cc u-hm e aa cc u ↔
      sAt e aa cc u (hm e aa cc u)+g*cc≤aa-1 := by
  have hi := (interval_iff e aa cc u (hm e aa cc u+g) hc).2
  have he : sAt e aa cc u (hm e aa cc u+g)=
      sAt e aa cc u (hm e aa cc u)+g*cc := by dsimp [sAt]; ring
  rw [he] at hi
  exact (show (g≤hp e aa cc u-hm e aa cc u) ↔
      hm e aa cc u+g≤hp e aa cc u by omega).trans hi

/-- A failed residue advances by exactly three quotients.  The representative
is in (0,C], so the equality case at C is not silently replaced by residue 0. -/
private theorem failed_step (aa cc e u : ℤ) (hc : 0<cc)
    (hlo : 3*cc<2*aa) (hhi : aa<2*cc)
    (hfail : aa-cc≤sAt e aa cc u (hm e aa cc u)) :
    sAt e aa cc (u+1) (hm e aa cc (u+1))=
      sAt e aa cc u (hm e aa cc u)+3*cc-2*aa := by
  have hb := hm_bounds e aa cc u hc
  have hq : 0<sAt e aa cc (u+1) (hm e aa cc u+3) ∧
      sAt e aa cc (u+1) (hm e aa cc u+3)≤cc := by
    have he : sAt e aa cc (u+1) (hm e aa cc u+3)=
        sAt e aa cc u (hm e aa cc u)+3*cc-2*aa := by dsimp [sAt]; ring
    rw [he]
    constructor <;> omega
  have hd : hm e aa cc (u+1)=hm e aa cc u+3 := by
    have hdiv : (e+2*(u+1)*aa)/cc=hm e aa cc u+3-1 := by
      apply (Int.ediv_eq_iff_of_pos hc).mpr
      dsimp [sAt] at hq
      constructor <;> nlinarith only [hq.1,hq.2]
    change (e+2*(u+1)*aa)/cc+1=hm e aa cc u+3
    rw [hdiv]
    ring
  rw [hd]
  dsimp [sAt]
  ring

private theorem three_residue (aa cc e : ℤ) (hc : 0<cc)
    (hlo : 8*cc<5*aa) (hhi : aa<2*cc) :
    ∃ u : ℕ, u≤2 ∧ 1≤hp e aa cc u-hm e aa cc u := by
  have h3 : 3*cc<2*aa := by omega
  by_cases h0 : 1≤hp e aa cc 0-hm e aa cc 0
  · exact ⟨0,by omega,h0⟩
  by_cases h1 : 1≤hp e aa cc 1-hm e aa cc 1
  · exact ⟨1,by omega,h1⟩
  have f0 : aa-cc≤sAt e aa cc 0 (hm e aa cc 0) := by
    have hi := width_iff e aa cc 0 1 hc
    omega
  have f1 : aa-cc≤sAt e aa cc 1 (hm e aa cc 1) := by
    have hi := width_iff e aa cc 1 1 hc
    omega
  have h01 := failed_step aa cc e 0 hc h3 hhi f0
  have h12 := failed_step aa cc e 1 hc h3 hhi f1
  have hb0 := hm_bounds e aa cc 0 hc
  refine ⟨2,by omega,(width_iff e aa cc 2 1 hc).mpr ?_⟩
  norm_num only at h01 h12
  omega

private theorem two_residue (aa cc e : ℤ) (hc : 0<cc)
    (hlo : 5*cc<3*aa) (hhi : aa<2*cc) :
    ∃ u : ℕ, u≤1 ∧ 1≤hp e aa cc u-hm e aa cc u := by
  by_cases h0 : 1≤hp e aa cc 0-hm e aa cc 0
  · exact ⟨0,by omega,h0⟩
  have f0 : aa-cc≤sAt e aa cc 0 (hm e aa cc 0) := by
    have hi := width_iff e aa cc 0 1 hc
    omega
  have h01 := failed_step aa cc e 0 hc (by omega) hhi f0
  have hb0 := hm_bounds e aa cc 0 hc
  refine ⟨1,by omega,(width_iff e aa cc 1 1 hc).mpr ?_⟩
  norm_num only at h01
  omega

private theorem trial_width (e aa cc u h : ℤ) (hc : 0<cc)
    (hlo : 0<sAt e aa cc u h) (hhi : sAt e aa cc u (h+1)≤aa-1) :
    1≤hp e aa cc u-hm e aa cc u := by
  have h0 := (interval_iff e aa cc u h hc).1.mpr hlo
  have h1 := (interval_iff e aa cc u (h+1) hc).2.mpr hhi
  omega

private theorem pow_one_two_four (n : ℕ) :
    (2:ℤ)^n=1 ∨ (2:ℤ)^n=2 ∨ 4≤(2:ℤ)^n := by
  by_cases h0 : n=0
  · subst n; norm_num
  by_cases h1 : n=1
  · subst n; norm_num
  right; right
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 2≤n by omega)
  norm_num at hp
  exact hp

private structure PowerData (a b c d : ℕ) : Prop where
  x4 : 4≤x a
  x_cases : x a=4 ∨ 8≤x a
  R1 : 1≤R a d
  R_cases : R a d=1 ∨ R a d=2 ∨ 4≤R a d
  r2 : 2≤r c d
  r_cases : r c d=2 ∨ 4≤r c d
  rle : r c d≤x a
  lam1 : 1≤lam b c
  t_eq : t d=2*x a*R a d
  z_eq : z c=r c d*t d
  y_eq : y b=2*lam b c*z c

private theorem power_data (a b c d : ℕ)
    (ha : 2≤a) (had : a<d) (hdc : d<c) (hcb : c<b) (hmoder : c≤a+d) :
    PowerData a b c d := by
  have xt : t d=2*x a*R a d := by
    dsimp [t,x,R]
    conv_lhs => rw [show d=a+(d-a-1)+1 by omega,pow_succ,pow_add]
    ring
  have zt : z c=r c d*t d := by
    dsimp [z,r,t]
    rw [←pow_add,show c-d+d=c by omega]
  have yz : y b=2*lam b c*z c := by
    dsimp [y,lam,z]
    conv_lhs => rw [show b=(b-c-1)+c+1 by omega,pow_succ,pow_add]
    ring
  have x4 : 4≤x a := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha
    norm_num at hp
    exact hp
  have xc : x a=4 ∨ 8≤x a := by
    by_cases h : a=2
    · left; simp [x,h]
    · right
      have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 3≤a by omega)
      norm_num at hp
      exact hp
  have r2 : 2≤r c d := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤c-d by omega)
    norm_num at hp
    exact hp
  refine ⟨x4,xc,?_,pow_one_two_four (d-a-1),r2,?_,?_,?_,xt,zt,yz⟩
  · dsimp [R]; exact one_le_pow₀ (by norm_num)
  · rcases pow_one_two_four (c-d) with h|h|h
    · dsimp [r] at r2; omega
    · exact Or.inl h
    · exact Or.inr h
  · exact pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show c-d≤a by omega)
  · dsimp [lam]; exact one_le_pow₀ (by norm_num)

private structure BasicBounds (X Y Z T la : ℤ) : Prop where
  apos : 0<A X Y Z
  bpos : 0<B X Y T
  cpos : 0<C X Z T la
  npos : 0<N X Y Z T
  ab : 0<A X Y Z-B X Y T
  cb : 0<C X Z T la-B X Y T
  bc : 0<2*B X Y T-C X Z T la
  kb : 0<K Y Z T-B X Y T
  epos : 0<E X Y Z T
  svb : 0<la*(2*L X Z T-Z-1)-B X Y T
  third_low : 0<(2*B X Y T-1)-la*(2*L X Z T-Z-1)
  third_high : 0<2*la*(2*L X Z T-Z-1)-(2*B X Y T-1)

/-- Positive polynomial certificates after exact nonnegative substitutions.
No relation between A/C is used in this full-domain lemma. -/
private theorem basic_bounds (X Y Z T la : ℤ)
    (hx : 4≤X) (ht : 2*X≤T) (hz : 2*T≤Z) (hl : 1≤la)
    (hy : Y=2*la*Z) : BasicBounds X Y Z T la := by
  subst Y
  obtain ⟨v,hv,rfl⟩ := exists_nonneg_add_of_le hx
  obtain ⟨w,hw,rfl⟩ := exists_nonneg_add_of_le ht
  obtain ⟨q,hq,rfl⟩ := exists_nonneg_add_of_le hz
  obtain ⟨l,hl',rfl⟩ := exists_nonneg_add_of_le hl
  constructor <;> dsimp [A,B,C,L,K,N,E] <;> ring_nf <;> positivity

private theorem paid_width (X Y Z T la rr : ℤ)
    (hx : 4≤X) (ht : 2*X≤T) (hr : 2≤rr) (hrx : rr≤X)
    (hz : Z=rr*T) (hl : 1≤la) (hy : Y=2*la*Z) :
    1<A X Y Z-(rr-1)*C X Z T la ∧
      A X Y Z<rr*la*(2*L X Z T-Z-1) := by
  have t0 : 0≤T := by omega
  have z0 : 0≤Z := by rw [hz]; positivity
  have rz : rr≤Z := by
    rw [hz]
    nlinarith only [mul_nonneg (show 0≤rr by omega) (show 0≤T-1 by omega)]
  have xz : 4*X≤Z := by
    rw [hz]
    nlinarith only [mul_nonneg (show 0≤rr-2 by omega) t0,ht]
  have hr0 : 0≤rr-2 := by omega
  have hl0 : 0≤la-1 := by omega
  have hxr : 0≤X-rr := by omega
  have hzX : 0≤Z-X := by omega
  have hi : 0<(X+1-rr)*Z*(T+1)-(rr-1) := by
    have hp : 0≤(X-rr)*Z*(T+1) := by positivity
    have hzt : 0≤Z*T := by positivity
    nlinarith only [hp,hzt,rz]
  have hid : A X Y Z-(rr-1)*C X Z T la=
      X+1+2*la*((X+1-rr)*Z*(T+1)-(rr-1)) := by
    rw [hy,hz]; dsimp [A,C,L]; ring
  have hs : X+1<rr*(1+Z)+2*Z*(Z-X) := by
    have hp : 0≤(rr-2)*(1+Z) := by positivity
    have hq : 0≤2*Z*(Z-X) := by positivity
    nlinarith only [hp,hq,xz,hx]
  have hmul : rr*(1+Z)+2*Z*(Z-X)≤
      la*(rr*(1+Z)+2*Z*(Z-X)) := by
    have hp : 0≤(la-1)*(rr*(1+Z)+2*Z*(Z-X)) := by positivity
    nlinarith only [hp]
  have hs_id : rr*la*(2*L X Z T-Z-1)-A X Y Z=
      la*(rr*(1+Z)+2*Z*(Z-X))-X-1 := by
    rw [hy,hz]; dsimp [A,L]; ring
  exact ⟨by rw [hid]; nlinarith only [hx,mul_pos (by omega : 0<2*la) hi],
    by nlinarith only [hs_id,hs,hmul]⟩

private theorem allowed_transfer (X Y Z T m : ℤ)
    (hx : 4≤X) (hm : 2≤m) (ht : m*X≤T) (hz : 2*T≤Z)
    (hy : 2*Z≤Y) :
    0<2*(K Y Z T-m*A X Y Z)-D Y Z-1 ∧ m*A X Y Z<K Y Z T := by
  have hmx0 : 0≤m*X := mul_nonneg (by omega) (by omega)
  have t0 : 0≤T := by omega
  have z0 : 0≤Z := by omega
  have hx1 : 0<X-1 := by omega
  have hm0 : 0<m := by omega
  have htm : 0≤T-m*X := by omega
  have hbr : 1≤2*Z*(T-m*X)+Z-2*m*X+1 := by
    have hp : 0≤2*Z*(T-m*X) := by positivity
    nlinarith only [hp,hz,ht]
  have y0 : 0≤Y := by omega
  have hprod : Y≤Y*(2*Z*(T-m*X)+Z-2*m*X+1) := by
    nlinarith only [mul_nonneg y0 (show 0≤2*Z*(T-m*X)+Z-2*m*X by omega)]
  have hmx : 0<2*m*(X-1) := by positivity
  have hid : 2*(K Y Z T-m*A X Y Z)-D Y Z-1=
      Y*(2*Z*(T-m*X)+Z-2*m*X+1)-2*m*(X+1) := by
    dsimp [A,K,D]; ring
  have hpos : 0<2*(K Y Z T-m*A X Y Z)-D Y Z-1 := by
    nlinarith only [hid,hprod,hy,hz,ht,hmx]
  have hd : 0<D Y Z := by dsimp [D]; positivity
  exact ⟨hpos,by omega⟩

/-- The ratio bounds are deliberately confined to z=2t. -/
private theorem r_two_ratios (X T la : ℤ) (hx : 4≤X) (ht : 2*X≤T) (hl : 1≤la) :
    8*C X (2*T) T la<5*A X (2*la*(2*T)) (2*T) ∧
    A X (2*la*(2*T)) (2*T)<2*C X (2*T) T la := by
  obtain ⟨v,hv,rfl⟩ := exists_nonneg_add_of_le hx
  obtain ⟨w,hw,rfl⟩ := exists_nonneg_add_of_le ht
  obtain ⟨l,hl',rfl⟩ := exists_nonneg_add_of_le hl
  constructor <;> apply sub_pos.mp <;> dsimp [A,C,L] <;> ring_nf <;> positivity

private theorem r_two_ratio_five_thirds (X T la : ℤ)
    (hx : 8≤X) (ht : 2*X≤T) (hl : 1≤la) :
    5*C X (2*T) T la<3*A X (2*la*(2*T)) (2*T) := by
  obtain ⟨v,hv,rfl⟩ := exists_nonneg_add_of_le hx
  obtain ⟨w,hw,rfl⟩ := exists_nonneg_add_of_le ht
  obtain ⟨l,hl',rfl⟩ := exists_nonneg_add_of_le hl
  apply sub_pos.mp
  dsimp [A,C,L]; ring_nf; positivity

private theorem R_one_trials (X la : ℤ) (hx : 4≤X) (hl : 1≤la) :
    0<sAt (E X (2*la*(4*X)) (4*X) (2*X))
      (A X (2*la*(4*X)) (4*X)) (C X (4*X) (2*X) la) 0 (4*X-6) ∧
    sAt (E X (2*la*(4*X)) (4*X) (2*X))
      (A X (2*la*(4*X)) (4*X)) (C X (4*X) (2*X) la) 0 (4*X-5)≤
      A X (2*la*(4*X)) (4*X)-1 := by
  obtain ⟨v,hv,rfl⟩ := exists_nonneg_add_of_le hx
  obtain ⟨l,hl',rfl⟩ := exists_nonneg_add_of_le hl
  constructor
  · dsimp [sAt,E,N,A,B,K,C,L]; ring_nf; positivity
  · apply sub_nonneg.mp
    dsimp [sAt,E,N,A,B,K,C,L]; ring_nf; positivity

private theorem R_two_x_four_trials (la : ℤ) (hl : 1≤la) :
    0<sAt (E 4 (2*la*32) 32 16) (A 4 (2*la*32) 32) (C 4 32 16 la) 0 20 ∧
    sAt (E 4 (2*la*32) 32 16) (A 4 (2*la*32) 32) (C 4 32 16 la) 0 21≤
      A 4 (2*la*32) 32-1 := by
  dsimp [sAt,E,N,A,B,K,C,L]
  constructor <;> nlinarith only [hl]

private theorem selector_width (X Y Z T la rr RR : ℤ)
    (hx : 4≤X) (hxc : X=4 ∨ 8≤X) (hR : 1≤RR)
    (hRc : RR=1 ∨ RR=2 ∨ 4≤RR) (hr : 2≤rr)
    (hrc : rr=2 ∨ 4≤rr) (hrx : rr≤X) (hl : 1≤la)
    (ht : T=2*X*RR) (hz : Z=rr*T) (hy : Y=2*la*Z) :
    ∃ u : ℕ, u≤2 ∧ (u:ℤ)+1≤RR ∧
      max 1 (rr-2)≤hp (E X Y Z T) (A X Y Z) (C X Z T la) u-
        hm (E X Y Z T) (A X Y Z) (C X Z T la) u := by
  have htlo : 2*X≤T := by
    rw [ht]
    nlinarith only [mul_nonneg (show 0≤2*X by omega) (show 0≤RR-1 by omega)]
  have hzlo : 2*T≤Z := by
    rw [hz]
    nlinarith only [mul_nonneg (show 0≤rr-2 by omega) (show 0≤T by omega)]
  have hb := basic_bounds X Y Z T la hx htlo hzlo hl hy
  rcases hrc with hr2|hr4
  · have hz2 : Z=2*T := by rw [hz,hr2]
    have ratio := r_two_ratios X T la hx htlo hl
    have hc := hb.cpos
    simp only [hy,hz2] at hc ⊢
    have heR (u : ℕ) (hu : (u:ℤ)+1≤RR)
        (hw : 1≤hp (E X (2*la*(2*T)) (2*T) T)
          (A X (2*la*(2*T)) (2*T)) (C X (2*T) T la) u-
          hm (E X (2*la*(2*T)) (2*T) T)
          (A X (2*la*(2*T)) (2*T)) (C X (2*T) T la) u) (hu2 : u≤2) :
        ∃ u : ℕ, u≤2 ∧ (u:ℤ)+1≤RR ∧
          max 1 (rr-2)≤hp (E X (2*la*(2*T)) (2*T) T)
            (A X (2*la*(2*T)) (2*T)) (C X (2*T) T la) u-
            hm (E X (2*la*(2*T)) (2*T) T)
            (A X (2*la*(2*T)) (2*T)) (C X (2*T) T la) u := by
      exact ⟨u,hu2,hu,by simpa [hr2] using hw⟩
    rcases hRc with hR1|hR2|hR4
    · have ht1 : T=2*X := by rw [ht,hR1]; ring
      have trials := R_one_trials X la hx hl
      have hw := trial_width
        (E X (2*la*(4*X)) (4*X) (2*X))
        (A X (2*la*(4*X)) (4*X)) (C X (4*X) (2*X) la) 0 (4*X-6)
        (by simpa only [ht1,show 2*(2*X)=4*X by ring] using hc)
        trials.1 (by simpa only [show 4*X-6+1=4*X-5 by ring] using trials.2)
      apply heR 0 (by norm_num <;> omega) _ (by omega)
      simpa only [ht1,show 2*(2*X)=4*X by ring,Nat.cast_zero] using hw
    · rcases hxc with hx4|hx8
      · have ht16 : T=16 := by rw [ht,hR2,hx4]; norm_num
        have trials := R_two_x_four_trials la hl
        apply heR 0 (by norm_num <;> omega) _ (by omega)
        rw [hx4,ht16]
        exact trial_width _ _ _ 0 20 (by simpa [hx4,ht16] using hc)
          trials.1 (by simpa using trials.2)
      · have ht8 : 2*X≤T := htlo
        have ratios := r_two_ratio_five_thirds X T la hx8 ht8 hl
        obtain ⟨u,hu,hw⟩ := two_residue _ _ _ hc ratios ratio.2
        exact heR u (by rw [hR2]; exact_mod_cast (show u+1≤2 by omega)) hw (by omega)
    · obtain ⟨u,hu,hw⟩ := three_residue _ _ _ hc ratio.1 ratio.2
      exact heR u (by
        have hu' : (u:ℤ)≤2 := by exact_mod_cast hu
        omega) hw hu
  · have paid := (paid_width X Y Z T la rr hx htlo hr hrx hz hl hy).1
    have hq := hm_bounds (E X Y Z T) (A X Y Z) (C X Z T la) 0 hb.cpos
    refine ⟨0,by omega,by norm_num <;> omega,?_⟩
    have hg : max 1 (rr-2)=rr-2 := max_eq_right (by omega)
    rw [hg,width_iff _ _ _ _ _ hb.cpos]
    norm_num only [Nat.cast_zero]
    nlinarith only [paid,hq.2]

/-- Integer selector certificate, including the two different second-seam
expressions.  The final physical theorem still has exactly its original binders. -/
private structure Selected (a b c d : ℕ) where
  u : ℕ
  H : ℕ
  early : Bool
  u_le : u≤2
  allowed : u+1≤2^(d-a-1)
  Hlo : 1≤H
  Hhi : H≤2^c-2
  slo : 0<sAt (E (x a) (y b) (z c) (t d)) (A (x a) (y b) (z c))
    (C (x a) (z c) (t d) (lam b c)) u H
  shi : sAt (E (x a) (y b) (z c) (t d)) (A (x a) (y b) (z c))
    (C (x a) (z c) (t d) (lam b c)) u H≤A (x a) (y b) (z c)-1
  choice : (early=true ∧
      H=(hm (E (x a) (y b) (z c) (t d)) (A (x a) (y b) (z c))
        (C (x a) (z c) (t d) (lam b c)) u).toNat) ∨
    (early=false ∧
      H=(hp (E (x a) (y b) (z c) (t d)) (A (x a) (y b) (z c))
        (C (x a) (z c) (t d) (lam b c)) u).toNat)
  second_lo : 0<2*FAt (E (x a) (y b) (z c) (t d)) (A (x a) (y b) (z c))
    (C (x a) (z c) (t d) (lam b c)) (z c) (lam b c) u H+
      (if early then A (x a) (y b) (z c) else -A (x a) (y b) (z c))-1
  second_hi : 2*FAt (E (x a) (y b) (z c) (t d)) (A (x a) (y b) (z c))
    (C (x a) (z c) (t d) (lam b c)) (z c) (lam b c) u H+
      (if early then A (x a) (y b) (z c) else -A (x a) (y b) (z c))-1≤
        A (x a) (y b) (z c)-1

private theorem selector_arithmetic (a b c d : ℕ)
    (ha : 2≤a) (had : a<d) (hdc : d<c) (hcb : c<b) (hmoder : c≤a+d) :
    Nonempty (Selected a b c d) := by
  classical
  have p := power_data a b c d ha had hdc hcb hmoder
  let X := x a; let Y := y b; let Z := z c; let T := t d
  let la := lam b c; let rr := r c d; let RR := R a d
  let aa := A X Y Z; let cc := C X Z T la; let ee := E X Y Z T
  have ht : 2*X≤T := by
    change 2*x a≤t d
    rw [p.t_eq]
    nlinarith only [mul_nonneg (show 0≤2*x a by have := p.x4; omega)
      (show 0≤R a d-1 by have := p.R1; omega)]
  have hz : 2*T≤Z := by
    change 2*t d≤z c
    rw [p.z_eq]
    nlinarith only [mul_nonneg (show 0≤r c d-2 by have := p.r2; omega)
      (show 0≤t d by dsimp [t]; positivity)]
  have hb := basic_bounds X Y Z T la p.x4 ht hz p.lam1 p.y_eq
  have paid := paid_width X Y Z T la rr p.x4 ht p.r2 p.rle p.z_eq p.lam1 p.y_eq
  obtain ⟨u,hu,hRu,hw⟩ := selector_width X Y Z T la rr RR p.x4 p.x_cases
    p.R1 p.R_cases p.r2 p.r_cases p.rle p.lam1 p.t_eq p.z_eq p.y_eq
  let m : ℤ := 2*((u:ℤ)+1)
  have hmx : m*X≤T := by
    have hdiff : 0≤RR-((u:ℤ)+1) := by omega
    have hx0 : 0≤X := by have := p.x4; omega
    have hp : 0≤2*X*(RR-((u:ℤ)+1)) := by positivity
    have hteq : T=2*X*RR := p.t_eq
    dsimp [m]
    nlinarith only [hteq,hp]
  have hY : 2*Z≤Y := by
    rw [show Y=2*la*Z from p.y_eq]
    have hz0 : 0≤Z := by dsimp [Z,z]; positivity
    nlinarith only [mul_nonneg (show 0≤la-1 from sub_nonneg.mpr p.lam1) hz0]
  have htransfer := allowed_transfer X Y Z T m p.x4
    (by dsimp [m]; omega) hmx hz hY
  have hmA : m*aa<K Y Z T := htransfer.2
  have hc : 0<cc := hb.cpos
  have he : 0<ee := hb.epos
  have haapos : 0<aa := hb.apos
  let lo := hm ee aa cc u
  let hi := hp ee aa cc u
  have hw_exact : max 1 (rr-2)≤hi-lo := hw
  have hw1 : lo+1≤hi := by
    have hh : 1≤max 1 (rr-2) := le_max_left _ _
    omega
  have hlo : 0<lo := by
    have hd := Int.ediv_nonneg (show 0≤ee+2*(u:ℤ)*aa by positivity) hc.le
    dsimp [lo,hm]
    omega
  have range_end : aa<sAt ee aa cc u (Z-1) := by
    have hid : sAt ee aa cc u (Z-1)-aa=
        2*K Y Z T+B X Y T-cc-m*aa := by
      dsimp [sAt,ee,aa,cc,m,E,N,A,B,C,L,K]
      rw [show Y=2*la*Z from p.y_eq]
      ring
    nlinarith only [hid,hmA,hb.kb,hb.bc]
  have hhi : hi≤Z-2 := by
    have hh := (interval_iff ee aa cc u (Z-1) hc).2
    by_contra hn
    have hs : sAt ee aa cc u (Z-1)≤aa-1 := hh.mp (by omega)
    omega
  have hlo_range : 1≤lo ∧ lo≤Z-2 := by omega
  have hhi_range : 1≤hi ∧ hi≤Z-2 := by omega
  have hslo : 0<sAt ee aa cc u lo ∧ sAt ee aa cc u lo≤aa-1 := by
    exact ⟨(hm_bounds ee aa cc u hc).1,
      (interval_iff ee aa cc u lo hc).2.mp (by omega)⟩
  have hshi : 0<sAt ee aa cc u hi ∧ sAt ee aa cc u hi≤aa-1 := by
    exact ⟨(interval_iff ee aa cc u hi hc).1.mp (by omega),
      (interval_iff ee aa cc u hi hc).2.mp le_rfl⟩
  have step_pos : 0<la*(2*L X Z T-Z-1) := by
    nlinarith only [hb.svb,hb.bpos]
  have hgap : aa<2*(FAt ee aa cc Z la u hi-FAt ee aa cc Z la u lo) := by
    have hg : rr≤2*max 1 (rr-2) := by
      rcases p.r_cases with h|h
      · change rr=2 at h; rw [h]; norm_num
      · change 4≤rr at h
        rw [max_eq_right (by omega : 1≤rr-2)]
        omega
    have hprod : 0≤(2*(hi-lo)-rr)*(la*(2*L X Z T-Z-1)) := by
      have hh : 0≤2*(hi-lo)-rr := by omega
      exact mul_nonneg hh step_pos.le
    have hid : FAt ee aa cc Z la u hi-FAt ee aa cc Z la u lo=
        (hi-lo)*(la*(2*L X Z T-Z-1)) := by
      dsimp [FAt,sAt,ZAt,cc,C]; ring
    nlinarith only [hid,hprod,paid.2]
  have slack (h : ℤ) (hh : h≤Z-2) : 0<aa-2*ZAt Z la h-1 := by
    have x0 : 0≤X-2 := by have := p.x4; omega
    have z0 : 0<Z := by dsimp [Z,z]; positivity
    have hh' : 0<(X-1)*Z-h := by
      have hp : 0≤(X-2)*Z := mul_nonneg x0 z0.le
      nlinarith only [hp,hh]
    have hid : aa-2*ZAt Z la h-1=
        X-2+2*la*((X-1)*Z-h)*(Z+1) := by
      dsimp [aa,A,ZAt]
      rw [show Y=2*la*Z from p.y_eq]
      ring
    rw [hid]
    have la0 : 0<la := by have := p.lam1; omega
    positivity
  have zpositive (h : ℤ) (hh : 0≤h) : 0<ZAt Z la h := by
    have z0 : 0<Z := by dsimp [Z,z]; positivity
    have la0 : 0<la := by have := p.lam1; omega
    dsimp [ZAt]; positivity
  have huNat : u+1≤2^(d-a-1) := by
    change (u:ℤ)+1≤(2:ℤ)^(d-a-1) at hRu
    exact_mod_cast hRu
  have Hrange (h : ℤ) (hh : 1≤h ∧ h≤Z-2) :
      1≤h.toNat ∧ h.toNat≤2^c-2 := by
    have hcast : (h.toNat:ℤ)=h := Int.toNat_of_nonneg (by omega)
    have hnatlo : 1≤h.toNat := by exact_mod_cast (show (1:ℤ)≤(h.toNat:ℤ) by omega)
    have hnat : h.toNat+2≤2^c := by
      have hh' : (h.toNat:ℤ)+2≤(2:ℤ)^c := by
        change 1≤h ∧ h≤(2:ℤ)^c-2 at hh
        omega
      exact_mod_cast hh'
    exact ⟨hnatlo,by omega⟩
  by_cases early : FAt ee aa cc Z la u lo≤0
  · have hcast : (lo.toNat:ℤ)=lo := Int.toNat_of_nonneg (by omega)
    have hrange := Hrange lo hlo_range
    have tslo : 0<2*FAt ee aa cc Z la u lo+aa-1 := by
      have hs := slack lo hlo_range.2
      dsimp [FAt] at ⊢
      nlinarith only [hs,hslo.1]
    have tshi : 2*FAt ee aa cc Z la u lo+aa-1≤aa-1 := by omega
    refine ⟨⟨u,lo.toNat,true,hu,huNat,hrange.1,hrange.2,?_,?_,?_,?_,?_⟩⟩
    · change 0<sAt ee aa cc u (lo.toNat:ℤ); rw [hcast]; exact hslo.1
    · change sAt ee aa cc u (lo.toNat:ℤ)≤aa-1; rw [hcast]; exact hslo.2
    · exact Or.inl ⟨rfl,rfl⟩
    · change 0<2*FAt ee aa cc Z la u (lo.toNat:ℤ)+aa-1
      rw [hcast]; exact tslo
    · change 2*FAt ee aa cc Z la u (lo.toNat:ℤ)+aa-1≤aa-1
      rw [hcast]; exact tshi
  · have hcast : (hi.toNat:ℤ)=hi := Int.toNat_of_nonneg (by omega)
    have hrange := Hrange hi hhi_range
    have tslo : 0<2*FAt ee aa cc Z la u hi-aa-1 := by omega
    have tshi : 2*FAt ee aa cc Z la u hi-aa-1≤aa-1 := by
      have hz0 := zpositive hi (by omega)
      dsimp [FAt] at ⊢
      nlinarith only [hz0,hshi.2]
    refine ⟨⟨u,hi.toNat,false,hu,huNat,hrange.1,hrange.2,?_,?_,?_,?_,?_⟩⟩
    · change 0<sAt ee aa cc u (hi.toNat:ℤ); rw [hcast]; exact hshi.1
    · change sAt ee aa cc u (hi.toNat:ℤ)≤aa-1; rw [hcast]; exact hshi.2
    · exact Or.inr ⟨rfl,rfl⟩
    · change 0<2*FAt ee aa cc Z la u (hi.toNat:ℤ)-aa-1
      rw [hcast]; exact tslo
    · change 2*FAt ee aa cc Z la u (hi.toNat:ℤ)-aa-1≤aa-1
      rw [hcast]; exact tshi


private theorem outside_seams (a b c d : ℕ)
    (ha : 2≤a) (had : a<d) (hdc : d<c) (hcb : c<b) (hmoder : c≤a+d)
    (q : Selected a b c d) :
    let aa := A (x a) (y b) (z c)
    let bb := B (x a) (y b) (t d)
    let kk := K (y b) (z c) (t d)
    let dd := D (y b) (z c)
    let cc := C (x a) (z c) (t d) (lam b c)
    let vv := 2*L (x a) (z c) (t d)-z c-1
    let m : ℤ := 2*((q.u:ℤ)+1)
    (0<bb+kk-m*aa ∧ bb+kk-m*aa≤kk-1) ∧
    (0<2*(bb+kk-m*aa)-dd-1 ∧
      2*(bb+kk-m*aa)-dd-1≤2*kk-dd-1) ∧
    (0<2*bb-cc ∧ 2*bb-cc≤bb-1) ∧
    (0<2*((2*bb-1)-lam b c*vv) ∧
      2*((2*bb-1)-lam b c*vv)≤2*bb-2) := by
  dsimp only
  have p := power_data a b c d ha had hdc hcb hmoder
  have ht : 2*x a≤t d := by
    rw [p.t_eq]
    nlinarith only [mul_nonneg (show 0≤2*x a by have := p.x4; omega)
      (show 0≤R a d-1 by have := p.R1; omega)]
  have hz : 2*t d≤z c := by
    rw [p.z_eq]
    nlinarith only [mul_nonneg (show 0≤r c d-2 by have := p.r2; omega)
      (show 0≤t d by dsimp [t]; positivity)]
  have hb := basic_bounds (x a) (y b) (z c) (t d) (lam b c)
    p.x4 ht hz p.lam1 p.y_eq
  have hu : (q.u:ℤ)+1≤R a d := by
    dsimp [R]; exact_mod_cast q.allowed
  have hm : 2*((q.u:ℤ)+1)*x a≤t d := by
    rw [p.t_eq]
    nlinarith only [mul_nonneg (show 0≤2*x a by have := p.x4; omega)
      (show 0≤R a d-((q.u:ℤ)+1) by omega)]
  have hy : 2*z c≤y b := by
    rw [p.y_eq]
    nlinarith only [mul_nonneg (show 0≤lam b c-1 by have := p.lam1; omega)
      (show 0≤z c by dsimp [z]; positivity)]
  have hp := allowed_transfer (x a) (y b) (z c) (t d) (2*((q.u:ℤ)+1))
    p.x4 (by omega) hm hz hy
  have hma : A (x a) (y b) (z c)≤2*((q.u:ℤ)+1)*A (x a) (y b) (z c) := by
    nlinarith only [mul_nonneg (show 0≤2*((q.u:ℤ)+1)-1 by omega) hb.apos.le]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  all_goals nlinarith only [hp.1,hp.2,hma,hb.ab,hb.bpos,hb.bc,hb.cb,
    hb.third_low,hb.third_high]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakModerateThirdGap
