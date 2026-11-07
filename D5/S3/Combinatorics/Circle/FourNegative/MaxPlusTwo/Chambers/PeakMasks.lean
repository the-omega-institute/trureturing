/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/PeakMasks
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/PeakMasks
   mirror-E: none(waiver:internal-mask-bridge)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Physical peak masks with adjacent-ratio reserve and capacity bounds. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Peak

/-! The first peak seam advances V only at the adjacent dyadic ratio. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private seedZ from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private ceilpos rounded_reserve ceilpos_capacity mass_margin
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
open private power_two_ge
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
open private peak_direct_bounds peak_advance_bounds peak_middle_bounds peak_double_end
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Peak

private theorem low_mask_bits (s n : ℕ) (hs : s=2 ∨ s=3) :
    ∀ e, s.testBit e=true → (8*n+3).testBit e=true := by
  intro e he
  have he2 : e<2 := by
    rcases hs with rfl|rfl
    · have he' : ((2:ℕ)^1).testBit e=true := he
      simp only [Nat.testBit_two_pow,decide_eq_true_eq] at he'
      omega
    · have he' : (2^2-1:ℕ).testBit e=true := he
      simp only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq] at he'
      omega
  have hm : (8*n+3)%2^3=3 := by omega
  have h:=congrArg (fun x:ℕ => x.testBit e) hm
  simp only [Nat.testBit_mod_two_pow,show e<3 by omega,decide_true,Bool.true_and] at h
  rw [h]
  change (2^2-1:ℕ).testBit e=true
  simp only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
  exact he2

set_option maxHeartbeats 1000000 in
-- Dyadic division and the rounded adjacent case use the same reserve interval.
private theorem peak_first_masks (a b c s : ℕ)
    (ha : 2≤a) (hc : 2≤c) (hcb : c<b) (hs : s=2 ∨ s=3) :
    let R : ℕ:=2^a; let T : ℕ:=2^b; let Z : ℕ:=2^c
    let A:=seedZ a b c
    let e1:=2*(T:ℤ)*((R:ℤ)*T+R+1)
    let uv:=if 4*Z≤T then (2*T/Z+s,0) else
      let n:=ceilpos (e1-3*A) (8*A-2*e1)
      (8*n+3,n)
    uv.1<2^(b+1) ∧ uv.2<2^(c-1) ∧
    (∀ e, s.testBit e=true → uv.1.testBit e=true) ∧
    e1≤A*uv.1-2*e1*uv.2 ∧ A*uv.1-2*e1*uv.2≤2*e1-A := by
  let R : ℕ:=2^a
  let T : ℕ:=2^b
  let Z : ℕ:=2^c
  let A:=seedZ a b c
  let e1:=2*(T:ℤ)*((R:ℤ)*T+R+1)
  let H : ℕ:=2^(b-c+1)
  have hs23 : 2≤s ∧ s≤3 := by rcases hs with rfl|rfl <;> omega
  have hA : A=(R:ℤ)*T*Z+((R:ℤ)*T+R+1) := by
    dsimp [A,seedZ,R,T,Z]; push_cast; ring
  have hR4 : 4≤(R:ℤ):=power_two_ge a ha
  have hT4 : 4≤(T:ℤ):=power_two_ge b (by omega)
  have hZ4 : 4≤(Z:ℤ):=power_two_ge c hc
  have hratio : Z*H=2*T := by
    dsimp [Z,H,T]
    rw [←pow_add]
    rw [show c+(b-c+1)=b+1 by omega,pow_succ]
    ring
  have hH : 2*T/Z=H := by
    rw [←hratio]
    exact Nat.mul_div_right H (Nat.two_pow_pos _)
  change (if 4*Z≤T then (2*T/Z+s,0) else
      (8*ceilpos (e1-3*A) (8*A-2*e1)+3,ceilpos (e1-3*A) (8*A-2*e1))).1<2^(b+1) ∧
    (if 4*Z≤T then (2*T/Z+s,0) else
      (8*ceilpos (e1-3*A) (8*A-2*e1)+3,ceilpos (e1-3*A) (8*A-2*e1))).2<2^(c-1) ∧
    (∀ e, s.testBit e=true →
      (if 4*Z≤T then (2*T/Z+s,0) else
        (8*ceilpos (e1-3*A) (8*A-2*e1)+3,ceilpos (e1-3*A) (8*A-2*e1))).1.testBit e=true) ∧
    e1≤A*(if 4*Z≤T then (2*T/Z+s,0) else
      (8*ceilpos (e1-3*A) (8*A-2*e1)+3,ceilpos (e1-3*A) (8*A-2*e1))).1-
      2*e1*(if 4*Z≤T then (2*T/Z+s,0) else
        (8*ceilpos (e1-3*A) (8*A-2*e1)+3,ceilpos (e1-3*A) (8*A-2*e1))).2 ∧
    A*(if 4*Z≤T then (2*T/Z+s,0) else
      (8*ceilpos (e1-3*A) (8*A-2*e1)+3,ceilpos (e1-3*A) (8*A-2*e1))).1-
      2*e1*(if 4*Z≤T then (2*T/Z+s,0) else
        (8*ceilpos (e1-3*A) (8*A-2*e1)+3,ceilpos (e1-3*A) (8*A-2*e1))).2≤2*e1-A
  by_cases hdirect : 4*Z≤T
  · simp only [if_pos hdirect,Prod.fst,Prod.snd,hH,Nat.cast_zero,mul_zero,sub_zero]
    have hH8 : 8≤H := by
      have : 3≤b-c+1 := by
        by_contra hh
        have he : b=c+1 := by omega
        have ht : T=2*Z := by dsimp [T,Z]; rw [he,pow_succ]; ring
        have hz : 0<Z:=Nat.two_pow_pos _
        omega
      exact Nat.pow_le_pow_right Nat.zero_lt_two this
    have hp:=peak_direct_bounds (R:ℤ) (T:ℤ) (Z:ℤ) (H:ℤ) (s:ℤ)
      hR4 hT4 hZ4 (by exact_mod_cast hH8) (by exact_mod_cast hs23)
      (by exact_mod_cast hratio)
    dsimp only at hp
    rw [←hA] at hp
    change e1≤A*((H:ℤ)+s) ∧ A*((H:ℤ)+s)≤2*e1-A ∧ (H:ℤ)+s<2*T at hp
    have hcap : H+s<2^(b+1) := by
      have hh : H+s<2*T := by exact_mod_cast hp.2.2
      simpa only [T,pow_succ,Nat.mul_comm] using hh
    have hsub : ∀ e, s.testBit e=true → (H+s).testBit e=true := by
      have hlt : s<H := by omega
      have hor : s ||| H=s+H := Nat.or_two_pow_eq_add_of_lt hlt
      intro e he
      rw [Nat.add_comm,←hor,Nat.testBit_or,he]
      simp
    refine ⟨hcap,Nat.two_pow_pos _,hsub,?_,?_⟩
    · simpa only [Nat.cast_add] using hp.1
    · simpa only [Nat.cast_add] using hp.2.1
  · simp only [if_neg hdirect,Prod.fst,Prod.snd]
    have hbc : b=c+1 := by
      by_contra hh
      have he : c+2≤b := by omega
      have hpow:=Nat.pow_le_pow_right Nat.zero_lt_two he
      have h4 : (2:ℕ)^(c+2)=4*Z := by dsimp [Z]; rw [pow_add]; norm_num; ring
      rw [h4] at hpow
      exact hdirect hpow
    have hT : T=2*Z := by dsimp [T,Z]; rw [hbc,pow_succ]; ring
    let P : ℕ:=2^(c-1)
    have hP2 : 2≤P:=Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤c-1 by omega)
    have hZ : Z=2*P := by
      dsimp [Z,P]
      calc
        (2:ℕ)^c=2^((c-1)+1) := by congr 1; omega
        _=2*2^(c-1) := by rw [pow_succ]; ring
    have hZi : (Z:ℤ)=2*(P:ℤ) := by exact_mod_cast hZ
    have hTi : (T:ℤ)=2*(Z:ℤ) := by exact_mod_cast hT
    have hAi : A=2*(R:ℤ)*(Z:ℤ)^2+(2*(R:ℤ)*Z+R+1) := by rw [hA,hTi]; ring
    have he : e1=4*(Z:ℤ)*(2*(R:ℤ)*Z+R+1) := by dsimp [e1]; rw [hTi]; ring
    have hp:=peak_advance_bounds (R:ℤ) (P:ℤ) hR4 (by exact_mod_cast hP2)
    dsimp only at hp
    rw [←hZi,←hAi,←he] at hp
    let n:=ceilpos (e1-3*A) (8*A-2*e1)
    change 1≤n ∧ (n:ℤ)≤(P:ℤ)-1 ∧
      e1≤A*(8*n+3)-2*e1*n ∧ A*(8*n+3)-2*e1*n≤2*e1-A ∧
      (8*n+3:ℤ)≤4*Z-5 at hp
    have hucap : 8*n+3<2^(b+1) := by
      have h4 : (2:ℕ)^(b+1)=4*Z := by dsimp [Z]; rw [hbc,show c+1+1=c+2 by omega,pow_add]; norm_num; ring
      rw [h4]
      have hh : (8*n+3:ℕ)<4*Z := by exact_mod_cast (show (8*n+3:ℤ)<4*Z by omega)
      exact hh
    have hvcap : n<2^(c-1) := by
      change n<P
      exact_mod_cast (show (n:ℤ)<P by omega)
    refine ⟨hucap,hvcap,low_mask_bits s n hs,?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hp.2.2.1
    · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hp.2.2.2.1


set_option maxHeartbeats 1000000 in
-- The rounded W mask stays inside the complete physical W chain.
private theorem peak_last_masks (a b c s : ℕ)
    (ha : 2≤a) (hc : 2≤c) (hab : a<b) (hs : s=2 ∨ s=3)
    (hmid : let R : ℕ:=2^a; let T : ℕ:=2^b; let Z : ℕ:=2^c
      let A:=seedZ a b c; let e2:=2*(T:ℤ)*((R:ℤ)+1)*Z
      e2≤A*s ∧ A*s≤2*e2-A) :
    let R : ℕ:=2^a; let T : ℕ:=2^b; let Z : ℕ:=2^c
    let A:=seedZ a b c
    let e2:=2*(T:ℤ)*((R:ℤ)+1)*Z; let e3:=2*(T:ℤ)*(T:ℤ)*Z
    let uw:=if 4*R≤T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)
    uw.1<2^(b+1) ∧ uw.2<2^(b-1) ∧
    (∀ e, uw.1.testBit e=true → s.testBit e=true) ∧
    e3≤A*uw.1+2*e2*uw.2 ∧ A*uw.1+2*e2*uw.2≤2*e3-A := by
  let R : ℕ:=2^a
  let T : ℕ:=2^b
  let Z : ℕ:=2^c
  let A:=seedZ a b c
  let e2:=2*(T:ℤ)*((R:ℤ)+1)*Z
  let e3:=2*(T:ℤ)*(T:ℤ)*Z
  change e2≤A*s ∧ A*s≤2*e2-A at hmid
  have hs23 : 2≤s ∧ s≤3 := by rcases hs with rfl|rfl <;> omega
  have hR4 : 4≤(R:ℤ):=power_two_ge a ha
  have hT4 : 4≤(T:ℤ):=power_two_ge b (by omega)
  have hZ4 : 4≤(Z:ℤ):=power_two_ge c hc
  have hA : 0<A := by dsimp [A,seedZ]; positivity
  have he2 : 0<e2 := by dsimp [e2]; positivity
  have hscap : s<2^(b+1) := by
    have h8 : 8≤(2:ℕ)^(b+1):=Nat.pow_le_pow_right Nat.zero_lt_two (show 3≤b+1 by omega)
    omega
  change (if 4*R≤T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)).1<2^(b+1) ∧
    (if 4*R≤T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)).2<2^(b-1) ∧
    (∀ e, (if 4*R≤T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)).1.testBit e=true →
      s.testBit e=true) ∧
    e3≤A*(if 4*R≤T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)).1+
      2*e2*(if 4*R≤T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)).2 ∧
    A*(if 4*R≤T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)).1+
      2*e2*(if 4*R≤T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)).2≤2*e3-A
  by_cases hdirect : 4*R≤T
  · simp only [if_pos hdirect,Prod.fst,Prod.snd]
    have hr : 4*(R:ℤ)≤T := by exact_mod_cast hdirect
    have he32 : 2*e2≤e3 := by
      have h:=mul_nonneg (show 0≤2*(T:ℤ)*Z by positivity) (show 0≤(T:ℤ)-2*((R:ℤ)+1) by omega)
      dsimp [e2,e3]; nlinarith only [h]
    have hAs : A≤A*s := by
      have hss : (1:ℤ)≤s := by exact_mod_cast (show 1≤s by omega)
      nlinarith only [mul_nonneg hA.le (sub_nonneg.mpr hss)]
    have hp:=rounded_reserve A e2 e3 (A*s) hA he2 ⟨hAs,hmid.2⟩ he32
    let P : ℕ:=2^(b-1)
    have hTP : (T:ℤ)=2*(P:ℤ) := by
      have ht : T=2*P := by
        dsimp [T,P]
        calc
          (2:ℕ)^b=2^((b-1)+1) := by congr 1; omega
          _=2*2^(b-1) := by rw [pow_succ]; ring
      exact_mod_cast ht
    have hcap0 : e3-(s:ℤ)*A≤2*e2*(P-1) := by
      have hRT : 0≤(R:ℤ)*T-2*((R:ℤ)+1) := by
        have hh:=mul_nonneg (show 0≤(R:ℤ) by omega) (show 0≤(T:ℤ)-4 by omega)
        nlinarith only [hh,hR4]
      have hprod:=mul_nonneg (show 0≤2*(T:ℤ)*Z by positivity) hRT
      have hAs0 : 0≤A*(s:ℤ) := by positivity
      have hid : 2*e2*(P-1)-(e3-(s:ℤ)*A)=
          2*(T:ℤ)*Z*((R:ℤ)*T-2*((R:ℤ)+1))+A*s := by
        dsimp [e2,e3]
        linear_combination -2*(T:ℤ)*((R:ℤ)+1)*Z*(hTP)
      linarith only [hid,hprod,hAs0]
    have hwcap : ceilpos (e3-(s:ℤ)*A) (2*e2)<2^(b-1) := by
      apply lt_of_le_of_lt (ceilpos_capacity _ _ (P-1) (by omega) ?_)
        (Nat.sub_lt (Nat.two_pow_pos _) (by omega))
      rw [Nat.cast_sub (Nat.one_le_two_pow),Nat.cast_one]
      exact hcap0
    refine ⟨hscap,hwcap,(by intro e he; exact he),?_,?_⟩
    · simpa only [mul_comm (s:ℤ) A] using hp.1
    · simpa only [mul_comm (s:ℤ) A] using hp.2
  · simp only [if_neg hdirect,Prod.fst,Prod.snd,Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,zero_add]
    have hba : b=a+1 := by
      by_contra hh
      have he : a+2≤b := by omega
      have hpow:=Nat.pow_le_pow_right Nat.zero_lt_two he
      have h4 : (2:ℕ)^(a+2)=4*R := by dsimp [R]; rw [pow_add]; norm_num; ring
      rw [h4] at hpow
      exact hdirect hpow
    have hT : (T:ℤ)=2*(R:ℤ) := by
      have ht : T=2*R := by dsimp [T,R]; rw [hba,pow_succ]; ring
      exact_mod_cast ht
    have hp:=peak_double_end (R:ℤ) (Z:ℤ) hR4 hZ4
    have hAi : A=2*(R:ℤ)^2*Z+(2*(R:ℤ)^2+R+1) := by
      dsimp [A,seedZ]
      change (R:ℤ)*T*Z+(1+(R:ℤ)+(R:ℤ)*T)=_
      rw [hT]; ring
    have he2i : e2=4*(R:ℤ)*((R:ℤ)+1)*Z := by dsimp [e2]; rw [hT]; ring
    have he3i : e3=8*(R:ℤ)^2*Z := by dsimp [e3]; rw [hT]; ring
    dsimp only at hp
    rw [←hAi,←he2i,←he3i] at hp
    have h2 : 2≤(2:ℕ)^(b-1):=Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤b-1 by omega)
    exact ⟨Nat.two_pow_pos _,by omega,(by simp),hp⟩


set_option maxHeartbeats 1000000 in
-- The independently chosen first and last masks share the same actual middle reserve.
private theorem peak_masks (a b c : ℕ) (ha : 2≤a) (hc : 2≤c)
    (hab : a<b) (hcb : c<b) :
    let R : ℕ:=2^a; let T : ℕ:=2^b; let Z : ℕ:=2^c
    let A:=seedZ a b c
    let e1:=2*(T:ℤ)*((R:ℤ)*T+R+1)
    let e2:=2*(T:ℤ)*((R:ℤ)+1)*Z; let e3:=2*(T:ℤ)*(T:ℤ)*Z
    let s : ℕ:=if Z≤R then 2 else 3
    let uv:=if 4*Z≤T then (2*T/Z+s,0) else
      let n:=ceilpos (e1-3*A) (8*A-2*e1)
      (8*n+3,n)
    let uw:=if 4*R≤T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)
    uv.1<2^(b+1) ∧ s<2^(b+1) ∧ uw.1<2^(b+1) ∧
    uv.2<2^(c-1) ∧ uw.2<2^(b-1) ∧
    (∀ e, s.testBit e=true → uv.1.testBit e=true) ∧
    (∀ e, uw.1.testBit e=true → s.testBit e=true) ∧
    e1≤A*uv.1-2*e1*uv.2 ∧ A*uv.1-2*e1*uv.2≤2*e1-A ∧
    e2≤A*s ∧ A*s≤2*e2-A ∧
    e3≤A*uw.1+2*e2*uw.2 ∧ A*uw.1+2*e2*uw.2≤2*e3-A := by
  let R : ℕ:=2^a
  let T : ℕ:=2^b
  let Z : ℕ:=2^c
  let A:=seedZ a b c
  let e1:=2*(T:ℤ)*((R:ℤ)*T+R+1)
  let e2:=2*(T:ℤ)*((R:ℤ)+1)*Z
  let e3:=2*(T:ℤ)*(T:ℤ)*Z
  let s : ℕ:=if Z≤R then 2 else 3
  let uv:=if 4*Z≤T then (2*T/Z+s,0) else
    let n:=ceilpos (e1-3*A) (8*A-2*e1)
    (8*n+3,n)
  let uw:=if 4*R≤T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)
  have hs : s=2 ∨ s=3 := by dsimp [s]; split_ifs <;> simp
  have hscap : s<2^(b+1) := by
    have h4 : 4≤(2:ℕ)^(b+1):=Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤b+1 by omega)
    rcases hs with he|he <;> omega
  have hA : A=(R:ℤ)*T*Z+((R:ℤ)*T+R+1) := by
    dsimp [A,seedZ,R,T,Z]; push_cast; ring
  have hp:=peak_middle_bounds (R:ℤ) (T:ℤ) (Z:ℤ)
    (power_two_ge a ha) (power_two_ge b (by omega)) (power_two_ge c hc)
  dsimp only at hp
  rw [←hA] at hp
  have hmid : e2≤A*s ∧ A*s≤2*e2-A := by
    by_cases he : Z≤R
    · have hsi : s=2 := if_pos he
      rw [hsi]
      simpa only [Nat.cast_ofNat,mul_comm A 2] using hp.1 (by exact_mod_cast he)
    · have hac : a<c := by
        by_contra hh
        have hpow:=Nat.pow_le_pow_right Nat.zero_lt_two (show c≤a by omega)
        exact he hpow
      have hpow:=Nat.pow_le_pow_right Nat.zero_lt_two (show a+1≤c by omega)
      have hRZ : 2*R≤Z := by simpa only [R,Z,pow_succ,Nat.mul_comm] using hpow
      have hsi : s=3 := if_neg he
      rw [hsi]
      simpa only [Nat.cast_ofNat,mul_comm A 3] using hp.2 (by exact_mod_cast hRZ)
  have hfirst:=peak_first_masks a b c s ha hc hcb hs
  have hlast:=peak_last_masks a b c s ha hc hab hs hmid
  change uv.1<2^(b+1) ∧ uv.2<2^(c-1) ∧
    (∀ e, s.testBit e=true → uv.1.testBit e=true) ∧
    e1≤A*uv.1-2*e1*uv.2 ∧ A*uv.1-2*e1*uv.2≤2*e1-A at hfirst
  change uw.1<2^(b+1) ∧ uw.2<2^(b-1) ∧
    (∀ e, uw.1.testBit e=true → s.testBit e=true) ∧
    e3≤A*uw.1+2*e2*uw.2 ∧ A*uw.1+2*e2*uw.2≤2*e3-A at hlast
  exact ⟨hfirst.1,hscap,hlast.1,hfirst.2.1,hlast.2.1,
    hfirst.2.2.1,hlast.2.2.1,hfirst.2.2.2.1,hfirst.2.2.2.2,
    hmid.1,hmid.2,hlast.2.2.2.1,hlast.2.2.2.2⟩


private theorem peak_word (a b c : ℕ) (hab : a<b) (hcb : c<b) :
    let R : ℕ:=2^a; let T : ℕ:=2^b; let Z : ℕ:=2^c
    let A:=seedZ a b c
    let e1:=2*(T:ℤ)*((R:ℤ)*T+R+1)
    let e2:=2*(T:ℤ)*((R:ℤ)+1)*Z; let e3:=2*(T:ℤ)*(T:ℤ)*Z
    let s : ℕ:=if Z≤R then 2 else 3
    let uv:=if 4*Z≤T then (2*T/Z+s,0) else
      let n:=ceilpos (e1-3*A) (8*A-2*e1)
      (8*n+3,n)
    let uw:=if 4*R≤T then (s,ceilpos (e3-s*A) (2*e2)) else (0,1)
    baseWord a b c=chamberMaskedWord a b c (b+2) uv.1 s uw.1 uv.2 0 0 uw.2 := by
  have hnot : ¬(min a c≤b ∧ b≤max a c) := by
    have : max a c<b := max_lt hab hcb
    omega
  have hval : ¬b<min a c := by
    have := min_le_left a c
    omega
  have hd : max (max a b) c+2=b+2 := by
    rw [max_eq_right hab.le,max_eq_left hcb.le]
  have hd4 : (2:ℤ)^(b+2)=4*(2:ℤ)^b := by rw [pow_add]; norm_num; ring
  have hA : (2:ℤ)^a*2^b*2^c+2^a*2^b+2^a+1=seedZ a b c := by
    dsimp [seedZ]; ring
  have he1 : (2:ℤ)^(b+2)*(2^a*2^b+2^a+1)/2=
      2*(2:ℤ)^b*(2^a*2^b+2^a+1) := by
    rw [hd4]
    have he : 4*(2:ℤ)^b*(2^a*2^b+2^a+1)=2*(2*2^b*(2^a*2^b+2^a+1)) := by ring
    rw [he]; omega
  have he2 : (2:ℤ)^(b+2)*(2^a+1)*2^c/2=2*(2:ℤ)^b*(2^a+1)*2^c := by
    rw [hd4]
    have he : 4*(2:ℤ)^b*(2^a+1)*2^c=2*(2*2^b*(2^a+1)*2^c) := by ring
    rw [he]; omega
  have he3 : (2:ℤ)^(b+2)*2^b*2^c/2=2*(2:ℤ)^b*2^b*2^c := by
    rw [hd4]
    have he : 4*(2:ℤ)^b*2^b*2^c=2*(2*2^b*2^b*2^c) := by ring
    rw [he]; omega
  dsimp only [baseWord,baseBlocks]
  rw [if_neg hnot]
  simp only [extremaBlocks,if_neg hval,hd]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [hA,he1,he2,he3]
  rfl

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
