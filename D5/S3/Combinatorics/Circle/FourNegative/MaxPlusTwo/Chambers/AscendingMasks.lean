/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/AscendingMasks
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/AscendingMasks
   mirror-E: none(waiver:internal-mask-bridge)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Actual ascending rounded masks, their physical capacities and release bounds. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualStrong
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Ascending

/-! Rounding retains the complete ascending equality faces. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private seedZ from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private ceilpos ceilpos_bounds ceilpos_capacity rounded_reserve mass_margin
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
open private power_two_ge from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
open private ascending_first_bounds ascending_equal_end_V ascending_wide_V ascending_adjacent_V
  ascending_double_release_cap ascending_four_release_cap ascending_equal_release_cap released_reserve
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Ascending

private theorem ceilpos_zero (n den : ℤ) (hden : 0<den) (hn : n≤0) :
    ceilpos n den=0 := by
  have h:=ceilpos_capacity n den 0 hden (by simpa using hn)
  omega

set_option maxHeartbeats 1200000 in
private theorem ascending_v_masks (a b c : ℕ) (ha : 2≤a)
    (hab : a≤b) (hbc : b≤c) (hac : a<c) :
    let R : ℕ:=2^a; let T : ℕ:=2^b; let Z : ℕ:=2^c
    let A:=seedZ a b c; let e1:=2*(Z:ℤ)*((R:ℤ)*T+R+1)
    let e2:=2*((R:ℤ)+1)*(Z:ℤ)^2; let e3:=2*(T:ℤ)*(Z:ℤ)^2
    let v:=ceilpos (e2-3*A) (2*e1); let S:=3*A+2*e1*v
    v<2^(c-1) ∧ 2*A<e1 ∧ e1≤3*A ∧ 3*A≤2*e1-A ∧ 2*A<e3 ∧
      e2≤S ∧ S≤2*e2-A ∧ S<e2+2*e1 := by
  let R : ℕ:=2^a
  let T : ℕ:=2^b
  let Z : ℕ:=2^c
  let A:=seedZ a b c
  let C : ℤ:=(R:ℤ)*T+R+1
  let e1:=2*(Z:ℤ)*C
  let e2:=2*((R:ℤ)+1)*(Z:ℤ)^2
  let e3:=2*(T:ℤ)*(Z:ℤ)^2
  let v:=ceilpos (e2-3*A) (2*e1)
  let S:=3*A+2*e1*v
  have hR4 : 4≤(R:ℤ):=power_two_ge a ha
  have hT4 : 4≤(T:ℤ):=power_two_ge b (by omega)
  have hZ4 : 4≤(Z:ℤ):=power_two_ge c (by omega)
  have hZT : (T:ℤ)≤Z := by exact_mod_cast (Nat.pow_le_pow_right Nat.zero_lt_two hbc)
  have hZR : 2*(R:ℤ)≤Z := by
    have he : (2:ℕ)^(a+1)≤Z:=Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    have he' : 2*R≤Z := by simpa only [pow_succ,R,Nat.mul_comm] using he
    exact_mod_cast he'
  have hA : A=(R:ℤ)*T*Z+C := by dsimp [A,seedZ,R,T,Z,C]; push_cast; ring
  have hApos : 0<A := by rw [hA]; dsimp [C]; positivity
  have hCpos : 0<C := by dsimp [C]; positivity
  have he1pos : 0<e1 := by dsimp [e1]; positivity
  have he2pos : 0<e2 := by dsimp [e2]; positivity
  have hf:=ascending_first_bounds (R:ℤ) (T:ℤ) (Z:ℤ) hR4 hT4 hZ4 hZT hZR
  dsimp only at hf
  rw [←hA] at hf
  change 2*A<e1 ∧ e1≤3*A ∧ 3*A≤2*e1-A ∧ 2*A<e3 at hf
  have hround:=ceilpos_bounds (e2-3*A) (2*e1) (by omega)
  change e2-3*A≤2*e1*(v:ℤ) ∧ (0<v → 2*e1*((v:ℤ)-1)<e2-3*A) at hround
  have hlow : e2≤S := by dsimp [S]; linarith only [hround.1]
  have hsmall : S<e2+2*e1 := by
    by_cases hv : v=0
    · dsimp [S]; rw [hv,Nat.cast_zero,mul_zero,add_zero]
      linarith only [hf.1,hApos,he2pos]
    · have hh:=hround.2 (by omega)
      dsimp [S]; linarith only [hh]
  have hupp : S≤2*e2-A := by
    by_cases hbe : b=c
    · have hz : Z=T := by dsimp [Z,T]; rw [hbe]
      have hTR : 2*(R:ℤ)≤T := by rw [←hz]; exact hZR
      have hp:=ascending_equal_end_V (R:ℤ) (T:ℤ) hR4 hTR
      dsimp only at hp
      have hp' : e1≤e2 ∧ e2≤3*A := by
        dsimp only [e1,e2,C]
        rw [hA]
        dsimp only [C]
        rw [hz]
        exact hp
      have hv : v=0:=ceilpos_zero _ _ (by omega) (by linarith only [hp'.2])
      dsimp [S]; rw [hv,Nat.cast_zero,mul_zero,add_zero]
      linarith only [hf.1,hp'.1]
    · have h2T : 2*(T:ℤ)≤Z := by
        have he : (2:ℕ)^(b+1)≤Z:=Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
        have he' : 2*T≤Z := by simpa only [pow_succ,T,Nat.mul_comm] using he
        exact_mod_cast he'
      by_cases hadj : a=b ∧ c=a+1
      · obtain ⟨hab',hc'⟩:=hadj
        have ht : T=R := by dsimp [T,R]; rw [hab']
        have hz : Z=2*R := by dsimp [Z,R]; rw [hc',pow_succ]; ring
        have hAi : A=2*(R:ℤ)^3+((R:ℤ)^2+R+1) := by rw [hA]; dsimp [C]; rw [ht,hz]; push_cast; ring
        have he1 : e1=4*(R:ℤ)*((R:ℤ)^2+R+1) := by dsimp [e1,C]; rw [ht,hz]; push_cast; ring
        have he2 : e2=8*((R:ℤ)+1)*(R:ℤ)^2 := by dsimp [e2]; rw [hz]; push_cast; ring
        have hp:=ascending_adjacent_V (R:ℤ) hR4
        dsimp only at hp
        rw [←hAi,←he1,←he2] at hp
        have hvle : v≤1:=ceilpos_capacity _ _ 1 (by omega) (by simpa using hp.2.1)
        have hv : v=1 := by
          by_contra hh
          have hv0 : v=0 := by omega
          rw [hv0,Nat.cast_zero,mul_zero] at hround
          linarith only [hp.1,hround.1]
        dsimp [S]; rw [hv,Nat.cast_one,mul_one]
        exact hp.2.2.2
      · have h4R : 4*(R:ℤ)≤Z := by
          have he : a+2≤c := by omega
          have hh : (2:ℕ)^(a+2)≤Z:=Nat.pow_le_pow_right Nat.zero_lt_two he
          have hh' : 4*R≤Z := by simpa only [pow_add,R,show (2:ℕ)^2=4 by norm_num,Nat.mul_comm] using hh
          exact_mod_cast hh'
        have hp:=ascending_wide_V (R:ℤ) (T:ℤ) (Z:ℤ) hR4 hT4 h2T h4R
        change 2*e1≤e2 at hp
        exact (rounded_reserve A e1 e2 (3*A) hApos he1pos
          ⟨by omega,hf.2.2.1⟩ hp).2
  have hvCap : v<2^(c-1) := by
    let H : ℕ:=2^(c-1)
    have hH : 1≤H:=Nat.one_le_two_pow
    have hz : (Z:ℤ)=2*(H:ℤ) := by
      have hh : Z=2*H := by
        dsimp [Z,H]
        calc
          (2:ℕ)^c=2^((c-1)+1) := by congr 1; omega
          _=2*2^(c-1) := by rw [pow_succ]; ring
      exact_mod_cast hh
    have hm:=mass_margin (R:ℤ) (T:ℤ) (Z:ℤ) hR4 hT4 hZ4
    change 3*C<(R:ℤ)*T*Z at hm
    have hn : 0≤(R:ℤ)*T*Z-2*C := by linarith only [hm,hCpos]
    have hprod:=mul_nonneg (show 0≤2*(Z:ℤ) by omega) hn
    have hc : e2-3*A≤2*e1*((H-1:ℕ):ℤ) := by
      rw [Nat.cast_sub hH,Nat.cast_one]
      have he : 2*e1*((H:ℤ)-1)-(e2-3*A)=
          2*(Z:ℤ)*((R:ℤ)*T*Z-2*C)+3*A := by
        dsimp [e1,e2,C]; rw [hz]; ring
      linarith only [he,hprod,hApos]
    have hh:=ceilpos_capacity (e2-3*A) (2*e1) (H-1) (by omega) hc
    change v≤H-1 at hh
    change v<H
    omega
  exact ⟨hvCap,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2,hlow,hupp,hsmall⟩

set_option maxHeartbeats 1600000 in
private theorem ascending_w_masks (a b c : ℕ) (ha : 2≤a)
    (hab : a≤b) (hbc : b≤c) (hac : a<c) :
    let R : ℕ:=2^a; let T : ℕ:=2^b; let Z : ℕ:=2^c
    let A:=seedZ a b c; let e1:=2*(Z:ℤ)*((R:ℤ)*T+R+1)
    let e2:=2*((R:ℤ)+1)*(Z:ℤ)^2; let e3:=2*(T:ℤ)*(Z:ℤ)^2
    let v:=ceilpos (e2-3*A) (2*e1); let S:=3*A+2*e1*v
    let wl:=if 4*R≤T then (ceilpos (e3-S) (2*e2),0)
      else if T=2*R then
        if e3≤S then (0,0) else (1,ceilpos (S+2*e2-2*e3+A) A)
      else (0,ceilpos (S-2*e3+A) A)
    wl.1<2^(b-1) ∧ wl.2≤3 ∧
      e3≤S+2*e2*wl.1-A*wl.2 ∧ S+2*e2*wl.1-A*wl.2≤2*e3-A := by
  let R : ℕ:=2^a
  let T : ℕ:=2^b
  let Z : ℕ:=2^c
  let A:=seedZ a b c
  let e1:=2*(Z:ℤ)*((R:ℤ)*T+R+1)
  let e2:=2*((R:ℤ)+1)*(Z:ℤ)^2
  let e3:=2*(T:ℤ)*(Z:ℤ)^2
  let v:=ceilpos (e2-3*A) (2*e1)
  let S:=3*A+2*e1*v
  have hv:=ascending_v_masks a b c ha hab hbc hac
  change v<2^(c-1) ∧ 2*A<e1 ∧ e1≤3*A ∧ 3*A≤2*e1-A ∧ 2*A<e3 ∧
    e2≤S ∧ S≤2*e2-A ∧ S<e2+2*e1 at hv
  have hR4 : 4≤(R:ℤ):=power_two_ge a ha
  have hT4 : 4≤(T:ℤ):=power_two_ge b (by omega)
  have hZ4 : 4≤(Z:ℤ):=power_two_ge c (by omega)
  have hA : A=(R:ℤ)*T*Z+((R:ℤ)*T+R+1) := by dsimp [A,seedZ,R,T,Z]; push_cast; ring
  have hApos : 0<A := by rw [hA]; positivity
  have he2pos : 0<e2 := by dsimp [e2]; positivity
  have hSpos : 0<S := by
    dsimp [S]
    have hn : 0≤2*e1*(v:ℤ) := by dsimp [e1]; positivity
    linarith only [hn,hApos]
  have hSA : A≤S := by
    dsimp [S]
    have hn : 0≤2*e1*(v:ℤ) := by dsimp [e1]; positivity
    linarith only [hn,hApos]
  let wl:=if 4*R≤T then (ceilpos (e3-S) (2*e2),0)
    else if T=2*R then
      if e3≤S then (0,0) else (1,ceilpos (S+2*e2-2*e3+A) A)
    else (0,ceilpos (S-2*e3+A) A)
  change wl.1<2^(b-1) ∧ wl.2≤3 ∧
    e3≤S+2*e2*wl.1-A*wl.2 ∧ S+2*e2*wl.1-A*wl.2≤2*e3-A
  dsimp only [wl]
  by_cases hwide : 4*R≤T
  · simp only [if_pos hwide,Prod.fst,Prod.snd,Nat.cast_zero,mul_zero,sub_zero]
    have hwidei : 4*(R:ℤ)≤T := by exact_mod_cast hwide
    have he : 2*e2≤e3 := by
      have h:=mul_nonneg (show 0≤(Z:ℤ)^2 by positivity) (show 0≤(T:ℤ)-2*((R:ℤ)+1) by omega)
      dsimp [e2,e3]; nlinarith only [h]
    have hres:=rounded_reserve A e2 e3 S hApos he2pos
      ⟨hSA,hv.2.2.2.2.2.2.1⟩ he
    have hcap : ceilpos (e3-S) (2*e2)<2^(b-1) := by
      let H : ℕ:=2^(b-1)
      have hH : 1≤H:=Nat.one_le_two_pow
      have ht : (T:ℤ)=2*(H:ℤ) := by
        have hh : T=2*H := by
          dsimp [T,H]
          calc
            (2:ℕ)^b=2^((b-1)+1) := by congr 1; omega
            _=2*2^(b-1) := by rw [pow_succ]; ring
        exact_mod_cast hh
      have hcoef : 0≤(R:ℤ)*T-2*((R:ℤ)+1) := by
        have h:=mul_nonneg (show 0≤(R:ℤ) by omega) (show 0≤(T:ℤ)-4 by omega)
        nlinarith only [h,hR4]
      have hp:=mul_nonneg (show 0≤2*(Z:ℤ)^2 by positivity) hcoef
      have hc : e3-S≤2*e2*((H-1:ℕ):ℤ) := by
        rw [Nat.cast_sub hH,Nat.cast_one]
        have hid : 2*e2*((H:ℤ)-1)-(e3-S)=
            2*(Z:ℤ)^2*((R:ℤ)*T-2*((R:ℤ)+1))+S := by
          dsimp [e2,e3]; rw [ht]; ring
        linarith only [hid,hp,hSpos]
      have hh:=ceilpos_capacity (e3-S) (2*e2) (H-1) (by omega) hc
      change ceilpos (e3-S) (2*e2)<H
      omega
    exact ⟨hcap,by omega,hres⟩
  · simp only [if_neg hwide]
    have hbsmall : b≤a+1 := by
      by_contra hh
      have hp:=Nat.pow_le_pow_right Nat.zero_lt_two (show a+2≤b by omega)
      have he : (2:ℕ)^(a+2)=4*R := by dsimp [R]; rw [pow_add]; norm_num; ring
      rw [he] at hp
      exact hwide hp
    by_cases hba : b=a+1
    · have ht : T=2*R := by dsimp [T,R]; rw [hba,pow_succ]; ring
      have hti : (T:ℤ)=2*(R:ℤ) := by exact_mod_cast ht
      simp only [if_pos ht]
      by_cases hready : e3≤S
      · simp only [if_pos hready,Prod.fst,Prod.snd,Nat.cast_zero,mul_zero,sub_zero,add_zero]
        have he : e2≤e3 := by
          have hp:=mul_nonneg (show 0≤(Z:ℤ)^2 by positivity) (show 0≤(R:ℤ)-1 by omega)
          dsimp [e2,e3]; rw [hti]; nlinarith only [hp]
        exact ⟨Nat.two_pow_pos _,by omega,hready,by linarith only [hv.2.2.2.2.2.2.1,he]⟩
      · simp only [if_neg hready,Prod.fst,Prod.snd,Nat.cast_one,mul_one]
        have hcap : S≤2*e3-2*e2+2*A := by
          by_cases hcnear : c=a+1
          · have hz : (Z:ℤ)=2*(R:ℤ) := by
              have hh : Z=2*R := by dsimp [Z,R]; rw [hcnear,pow_succ]; ring
              exact_mod_cast hh
            have hnear : 2*(Z:ℤ)^2≤A := by
              rw [hA,hti,hz]
              have hr : 0≤(R:ℤ)-4 := by omega
              generalize he : (R:ℤ)-4=r at hr
              have hR : (R:ℤ)=r+4 := by omega
              rw [hR]
              apply sub_nonneg.mp
              ring_nf; positivity
            have hid : 2*e2-e3=4*(Z:ℤ)^2 := by dsimp [e2,e3]; rw [hti]; ring
            linarith only [hready,hnear,hid]
          · have h4Z : 4*(R:ℤ)≤Z := by
              have hp:=Nat.pow_le_pow_right Nat.zero_lt_two (show a+2≤c by omega)
              have he : (2:ℕ)^(a+2)=4*R := by dsimp [R]; rw [pow_add]; norm_num; ring
              rw [he] at hp
              exact_mod_cast hp
            by_cases ha2 : a=2
            · by_cases hc4 : c=4
              · norm_num [S,v,A,seedZ,e1,e2,e3,R,T,Z,ha2,hba,hc4,ceilpos]
              · by_cases hc5 : c=5
                · norm_num [S,v,A,seedZ,e1,e2,e3,R,T,Z,ha2,hba,hc5,ceilpos]
                · have hz64 : (64:ℤ)≤Z := by
                    exact_mod_cast (Nat.pow_le_pow_right Nat.zero_lt_two (show 6≤c by omega))
                  have hp:=ascending_four_release_cap (Z:ℤ) hz64
                  have hr : (R:ℤ)=4 := by norm_num [R,ha2]
                  have ht8 : (T:ℤ)=8 := by rw [hti,hr]; norm_num
                  have hAi : A=32*(Z:ℤ)+37 := by rw [hA,hr,ht8]; ring
                  have he1 : e1=74*(Z:ℤ) := by dsimp [e1]; rw [hr,ht8]; ring
                  have he2 : e2=10*(Z:ℤ)^2 := by dsimp [e2]; rw [hr]; ring
                  have he3 : e3=16*(Z:ℤ)^2 := by dsimp [e3]; rw [ht8]; ring
                  dsimp only at hp
                  rw [←hAi,←he1,←he2,←he3] at hp
                  linarith only [hv.2.2.2.2.2.2.2,hp]
            · have hR8 : (8:ℤ)≤R := by
                exact_mod_cast (Nat.pow_le_pow_right Nat.zero_lt_two (show 3≤a by omega))
              have hp:=ascending_double_release_cap (R:ℤ) (Z:ℤ) hR8 h4Z
              have hAi : A=2*(R:ℤ)^2*Z+(2*(R:ℤ)^2+R+1) := by rw [hA,hti]; ring
              have he1 : e1=2*(Z:ℤ)*(2*(R:ℤ)^2+R+1) := by dsimp [e1]; rw [hti]; ring
              have he3 : e3=4*(R:ℤ)*(Z:ℤ)^2 := by dsimp [e3]; rw [hti]; ring
              dsimp only at hp
              rw [←hAi,←he1,←he3] at hp
              change e2+2*e1≤2*e3-2*e2+2*A at hp
              linarith only [hv.2.2.2.2.2.2.2,hp]
        have he : e3≤S+2*e2 := by
          have hp : 0≤(Z:ℤ)^2 := by positivity
          have hid : 2*e2-e3=4*(Z:ℤ)^2 := by dsimp [e2,e3]; rw [hti]; ring
          linarith only [hp,hid,hSpos]
        have hr:=released_reserve A e3 (S+2*e2) hApos (by linarith only [hv.2.2.2.2.1]) he
          (by linarith only [hcap])
        have h1cap : 1<2^(b-1) := by
          have hh : 2≤(2:ℕ)^(b-1):=Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤b-1 by omega)
          omega
        exact ⟨h1cap,hr⟩
    · have hb0 : b=a := by omega
      have ht : T=R := by dsimp [T,R]; rw [hb0]
      have hnot : ¬T=2*R := by have hp : 0<R:=Nat.two_pow_pos _; omega
      simp only [if_neg hnot,Prod.fst,Prod.snd,Nat.cast_zero,mul_zero,add_zero]
      have hti : (T:ℤ)=(R:ℤ) := by exact_mod_cast ht
      have h2Z : 2*(R:ℤ)≤Z := by
        have hp:=Nat.pow_le_pow_right Nat.zero_lt_two (show a+1≤c by omega)
        have he : (2:ℕ)^(a+1)=2*R := by dsimp [R]; rw [pow_succ]; ring
        rw [he] at hp
        exact_mod_cast hp
      have hp:=ascending_equal_release_cap (R:ℤ) (Z:ℤ) hR4 h2Z
      have hAi : A=(R:ℤ)^2*Z+((R:ℤ)^2+R+1) := by rw [hA,hti]; ring
      have he1 : e1=2*(Z:ℤ)*((R:ℤ)^2+R+1) := by dsimp [e1]; rw [hti]; ring
      have he3 : e3=2*(R:ℤ)*(Z:ℤ)^2 := by dsimp [e3]; rw [hti]
      dsimp only at hp
      rw [←hAi,←he1,←he3] at hp
      change e2+2*e1≤2*e3+2*A at hp
      have he : e3≤S := by
        have hh : 0≤(Z:ℤ)^2 := by positivity
        have hid : e2-e3=2*(Z:ℤ)^2 := by dsimp [e2,e3]; rw [hti]; ring
        linarith only [hh,hid,hv.2.2.2.2.2.1]
      have hr:=released_reserve A e3 S hApos (by linarith only [hv.2.2.2.2.1]) he
        (by linarith only [hp,hv.2.2.2.2.2.2.2])
      exact ⟨Nat.two_pow_pos _,hr⟩

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
