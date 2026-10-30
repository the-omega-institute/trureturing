/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeStrictDescendingJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeStrictDescendingJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Full strict descending physical three-gap chamber with an ear after gamma. -/
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

/-! Physical masks and asymmetric landing estimates for all descending dyadic gaps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeStrictDescendingJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open private Mask Mask.mk Mask.u Mask.v Mask.w Negative Negative.alpha Negative.beta Negative.gamma
  Order Order.agb Order.first Order.middle Order.last Ear Ear.t
  Plan Plan.p Plan.t Plan.order Plan.ear makePlan atNegative
  oldMass newMass cap oldHeight newHeight Bounded Separate Seams Certificate
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks
open private realize from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

private theorem singleton_complement (n i w : ℕ) (hw : w < 2^n)
    (hi : w.testBit i = true) :
    Disjoint (2^i).bitIndices.toFinset (2^n-1-w).bitIndices.toFinset := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  have he : j = i := by simpa using hj
  subst j
  have hh := Nat.mem_bitIndices.mp (List.mem_toFinset.mp hk)
  have he : 2^n-1-w = 2^n-(w+1) := by omega
  rw [he, Nat.testBit_two_pow_sub_succ hw, hi] at hh
  simp at hh

private theorem near_bit (h i : ℕ) (hi : i=h ∨ i=h+1) :
    (3*2^h).testBit i = true := by
  apply Nat.mem_bitIndices.mp
  rw [Nat.mul_comm, Nat.bitIndices_two_pow_mul]
  rcases hi with rfl | rfl
  · exact List.mem_map.mpr ⟨0, by decide, by omega⟩
  · exact List.mem_map.mpr ⟨1, by decide, by omega⟩

private theorem far_bit (h i : ℕ) (hi : i<h) :
    (3*2^h-1).testBit i = true := by
  have hp := Nat.two_pow_pos h
  have he : 3*2^h-1 = 2^(h+1)+(2^h-1) := by rw [pow_succ]; omega
  rw [he, Nat.testBit_two_pow_add_gt (by omega), Nat.testBit_two_pow_sub_one]
  simp [hi]

private def First (R S U p e : ℤ) : Prop :=
  let z := p*(1+2*U+4*U*R)-(1+2*R+4*R*S)+e*(1+2*S+4*S*U)
  0≤2*z-p-(2*S+1)*e ∧ z≤U+2*U*R
private def Second (R S U w : ℤ) : Prop :=
  0≤w*(1+2*S+8*S*U)+S+4*S*U-1-3*R-6*R*S ∧
  w*(1+2*S+4*S*U)+S+2*S*U-R-2*R*S≤R+2*R*S

private theorem seams_certificate (R S U p e w : ℤ)
    (hR : 1≤R) (hS : 1≤S) (hU : 1≤U)
    (hp : 1≤p) (hpS : p≤S) (he : 0≤e) (heR : e<R)
    (hw : 0≤w) (hwR : w<R)
    (hsep : Disjoint e.toNat.bitIndices.toFinset (R-1-w).toNat.bitIndices.toFinset)
    (hf : First R S U p e) (hg : Second R S U w) :
    Certificate (2*R) (2*S) (2*U)
      (makePlan 0 Order.agb Ear.t (Mask.mk (U-1) (p-1) e) (Mask.mk 0 0 (R-1-w))) := by
  obtain ⟨hz,hzupper⟩ := hf
  obtain ⟨hy,hyupper⟩ := hg
  have hdefect : 0≤(2*S+1)*e := mul_nonneg (by omega) he
  have hRS : 0≤R*S := mul_nonneg (by omega) (by omega)
  have hdefectW : 0≤(2*S+1)*w := mul_nonneg (by omega) hw
  have hhalf (x : ℤ) : 2*x/2=x := by omega
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]
    simp only [hhalf]
    exact ⟨by omega,by omega,by omega,by omega,he,heR⟩
  · dsimp [Bounded,makePlan]
    simp only [hhalf]
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
  · simpa [Separate,makePlan] using hsep
  · dsimp [Seams,makePlan,oldHeight,newHeight,oldMass,newMass,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hhalf, reduceCtorEq, ite_true, ite_false]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith only [hz,hzupper,hy,hyupper,hdefect,hdefectW,hp,hS,hR,hRS,hw]

private theorem first_two (U D : ℤ) (hU : 2≤U) (hD : 1≤D) :
    First (4*U*D) (2*U) U 2 D := by
  have hcoef : 0≤16*U^2-12*U+1 := by nlinarith
  have hlow := mul_nonneg (by omega : 0≤D) hcoef
  have hmargin := mul_nonneg (by omega : 0≤D-1) (by omega : 0≤4*U-1)
  constructor <;> nlinarith only [hlow,hmargin,hU]

private theorem first_four (U D : ℤ) (hU : 2≤U) (hD : 2≤D) :
    First (4*U*D) (4*U) U 2 (2*D) := by
  have hc : 6*U+2≤8*U^2-8*U-2 := by nlinarith [mul_nonneg (by omega : 0≤U-2) (by omega : 0≤8*U+2)]
  have hm := mul_nonneg (by omega : 0≤D-2) (by nlinarith : 0≤8*U^2-8*U-2)
  constructor <;> nlinarith only [hU,hD,hc,hm]

private theorem first_near (U D q : ℤ) (hU : 2≤U) (hq : 2≤q)
    (hqU : q≤U) (hD : 2*q≤D) :
    First (4*U*D) (4*q*U) U (3*q) D := by
  have hd : 0≤D := by omega
  have hl := mul_nonneg hd (show 0≤8*U*(q-2)+1 by positivity)
  have hm1 := mul_nonneg hd (mul_nonneg (by omega : 0≤8*U) (by omega : 0≤U-q))
  have hm2 := mul_nonneg (by omega : 0≤D-2*q) (by omega : 0≤8*U-1)
  have hm3 := mul_nonneg (by omega : 0≤q) (by omega : 0≤2*U-1)
  constructor <;> nlinarith only [hl,hm1,hm2,hm3,hU,hq]

private theorem first_far (U t m : ℤ) (hU : 2≤U) (ht : 2≤t) (hm : 2≤m) :
    First (2*m*U*t) (t*U) U t m := by
  have hu : 0≤U := by omega
  have ht0 : 0≤t := by omega
  have hlo := mul_nonneg (mul_nonneg (by omega : 0≤m) (mul_nonneg hu ht0)) (by omega : 0≤4*U-3)
  have hut : 1≤2*U*t := by nlinarith
  have hm1 := mul_nonneg (by omega : 0≤m-2) (by omega : 0≤2*U*t-1)
  have hm2 := mul_nonneg ht0 (by omega : 0≤2*U-1)
  constructor <;> nlinarith only [hlo,hm1,hm2,hU,ht,hm]

private theorem first_far_one (U t : ℤ) (hU : 2≤U) (ht : 8*U≤t) :
    First (2*U*t) (t*U) U (t-1) 2 := by
  have hcoef : 0≤4*U^2-2*U-1 := by nlinarith
  have hm := mul_nonneg (by omega : 0≤t) hcoef
  constructor <;> nlinarith only [hm,hU,ht]

private theorem second_upper (U D t w : ℤ) (hU : 2≤U) (ht : 2≤t)
    (hD : t≤2*D) (hw : w≤3*D) :
    w*(1+2*t*U+4*t*U^2)+t*U+2*t*U^2-4*U*D-8*U^2*D*t≤4*U*D+8*U^2*D*t := by
  have hu : 0≤U := by omega
  have ht0 : 0≤t := by omega
  have hc : 0≤2*U*t*(2*U-3)+8*U-3 := by
    have hp := mul_nonneg (mul_nonneg hu ht0) (by omega : 0≤2*U-3)
    nlinarith only [hp,hU]
  have hm1 := mul_nonneg (by omega : 0≤2*D-t) hc
  have hp0 : 4≤2*U*(t-1) := by nlinarith [mul_nonneg (by omega : 0≤U-2) (by omega : 0≤t-1)]
  have hp1 := mul_nonneg (by omega : 0≤2*U*(t-1)-4) (by omega : 0≤2*U-3)
  have hp2 : 0≤2*U*(t-1)*(2*U-3)-3 := by nlinarith only [hp1,hU]
  have hm2 := mul_nonneg ht0 hp2
  have hm3 := mul_nonneg (by omega : 0≤3*D-w) (show 0≤1+2*t*U+4*t*U^2 by positivity)
  nlinarith only [hm1,hm2,hm3]

private theorem second_near (U D t : ℤ) (hU : 2≤U) (hD : 1≤D) (ht : 2≤t) (hDt : t≤2*D) :
    Second (4*U*D) (t*U) U (3*D) := by
  constructor
  · have hcoef : 0≤2*t*U+1-4*U := by nlinarith [mul_nonneg (by omega : 0≤t-2) (by omega : 0≤U)]
    have hp := mul_nonneg (by omega : 0≤3*D) hcoef
    have hp1 : 1≤t*U := by nlinarith
    have hp2 := mul_nonneg (by omega : 0≤t) (sq_nonneg U)
    nlinarith only [hp,hp1,hp2]
  · convert second_upper U D t (3*D) hU ht (by omega) (by omega) using 1 <;> ring

private theorem second_far (U D t : ℤ) (hU : 2≤U) (hD : t≤2*D) (ht : 8*U≤t) :
    Second (4*U*D) (t*U) U (3*D-1) := by
  constructor
  · have hd : 4*U≤D := by omega
    have hut : 4≤t*U := by nlinarith
    have hc : 0≤t*U+1-4*U := by nlinarith [mul_nonneg (by omega : 0≤t-4) (by omega : 0≤U)]
    have hp1 := mul_nonneg (by omega : 0≤3*D) hc
    have hp2 := mul_nonneg (by omega : 0≤3*(D-4*U)) (by omega : 0≤t*U)
    have hp3 := mul_nonneg (by omega : 0≤t*U) (by omega : 0≤8*U-2)
    nlinarith only [hp1,hp2,hp3,hut]
  · convert second_upper U D t (3*D-1) hU (by omega) hD (by omega) using 1 <;> ring

/-- The full strict descending chamber, retaining the same physical permutation and literal ear. -/
theorem actualSource_three_negative_strict_descending_joint_lift (a b c : ℕ)
    (hc : 2≤c) (hcb : c<b) (hba : b<a) :
    ∃ sigma : List (Fin (a+b+c)), ∃ j : ℕ, j≤a+b+c ∧
      OriginalOrder (a+b+c) (1+2^a+2^(a+b)) sigma ∧
      OriginalOrder (a+b+c+1) (2*(1+2^a+2^(a+b))) (earWord (a+b+c) sigma j) := by
  let d := b-c
  let ell := a-b-1
  let h := a-c-2
  let U : ℤ := 2^(c-1)
  let t : ℤ := 2^d
  let m : ℤ := 2^ell
  let D : ℤ := 2^h
  let R : ℤ := 4*U*D
  let S : ℤ := t*U
  have hd : 1≤d := by dsimp [d]; omega
  have hU : 2≤U := by
    change (2:ℤ)^1≤2^(c-1)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have ht : 2≤t := by
    change (2:ℤ)^1≤2^d
    exact pow_le_pow_right₀ (by norm_num) hd
  have hm : 1≤m := by dsimp [m]; exact_mod_cast Nat.one_le_two_pow
  have hD : 1≤D := by dsimp [D]; exact_mod_cast Nat.one_le_two_pow
  have hu : (2:ℤ)^c=2*U := by
    calc
      (2:ℤ)^c=2^((c-1)+1) := by congr 1; omega
      _=2*U := by rw [pow_succ]; dsimp [U]; ring
  have hs : (2:ℤ)^b=2*S := by
    calc
      (2:ℤ)^b=2^(d+(c-1)+1) := by congr 1; dsimp [d]; omega
      _=2*S := by rw [pow_succ,pow_add]; dsimp [S,t,U]; ring
  have hr : (2:ℤ)^a=2*R := by
    calc
      (2:ℤ)^a=2^((c-1)+h+3) := by congr 1; dsimp [h]; omega
      _=2*R := by rw [pow_add,pow_add]; dsimp [R,U,D]; norm_num; ring
  have hrel : 2*D=m*t := by
    have he : h+1=ell+d := by dsimp [h,ell,d]; omega
    calc
      2*D=(2:ℤ)^(h+1) := by dsimp [D]; rw [pow_succ]; ring
      _=m*t := by rw [he,pow_add]
  have hDt : t≤2*D := by nlinarith [mul_nonneg (by omega : 0≤m-1) (by omega : 0≤t)]
  have hmD : m≤D := by nlinarith [mul_nonneg (by omega : 0≤m) (by omega : 0≤t-2)]
  have hRpow : R=(2:ℤ)^(a-1) := by
    have he : (2:ℤ)^a=2*2^(a-1) := by
      calc
        (2:ℤ)^a=2^((a-1)+1) := by congr 1; omega
        _=2*2^(a-1) := by rw [pow_succ]; ring
    omega
  have hS : 2≤S := by dsimp [S]; nlinarith
  have hRD : 3*D<R := by
    dsimp [R]
    nlinarith [mul_nonneg (by omega : 0≤U-2) (by omega : 0≤D)]
  have sep (i : ℕ) (e w : ℤ) (he : e=(2:ℤ)^i) (hw0 : 0≤w) (hwR : w<R)
      (hbit : w.toNat.testBit i=true) :
      Disjoint e.toNat.bitIndices.toFinset (R-1-w).toNat.bitIndices.toFinset := by
    have hwN : (w.toNat:ℤ)=w := Int.toNat_of_nonneg hw0
    have hncast : ((2^(a-1):ℕ):ℤ)=(2:ℤ)^(a-1) := by norm_cast
    have hn : w.toNat<2^(a-1) := by
      exact_mod_cast (show (w.toNat:ℤ)<(2:ℤ)^(a-1) by rw [hwN,←hRpow]; exact hwR)
    have heNat : e.toNat=2^i := by rw [he]; norm_cast
    have hcomp : (R-1-w).toNat=2^(a-1)-1-w.toNat := by omega
    rw [heNat,hcomp]
    exact singleton_complement (a-1) i w.toNat hn hbit
  have nearNat : (3*D).toNat=3*2^h := by
    dsimp [D]
    rw [Int.toNat_mul (by norm_num) (by positivity),Int.toNat_pow_of_nonneg (by norm_num)]
    rfl
  have farNat : (3*D-1).toNat=3*2^h-1 := by
    omega
  have nearSep (i : ℕ) (e : ℤ) (he : e=(2:ℤ)^i) (hi : i=h ∨ i=h+1) :
      Disjoint e.toNat.bitIndices.toFinset (R-1-3*D).toNat.bitIndices.toFinset := by
    apply sep i e (3*D) he (by omega) hRD
    rw [nearNat]
    exact near_bit h i hi
  have farSep (i : ℕ) (e : ℤ) (he : e=(2:ℤ)^i) (hi : i<h) :
      Disjoint e.toNat.bitIndices.toFinset (R-1-(3*D-1)).toNat.bitIndices.toFinset := by
    apply sep i e (3*D-1) he (by omega) (by omega)
    rw [farNat]
    exact far_bit h i hi
  have go (p e w : ℤ) (hp : 1≤p) (hpS : p≤S) (he : 0≤e) (heR : e<R)
      (hw : 0≤w) (hwR : w<R)
      (hsep : Disjoint e.toNat.bitIndices.toFinset (R-1-w).toNat.bitIndices.toFinset)
      (hf : First R S U p e) (hg : Second R S U w) :
      ∃ plan, Certificate (2*R) (2*S) (2*U) plan :=
    ⟨_,seams_certificate R S U p e w (by omega) (by omega) (by omega)
      hp hpS he heR hw hwR hsep hf hg⟩
  obtain ⟨plan,hcert⟩ : ∃ plan, Certificate (2*R) (2*S) (2*U) plan := by
    by_cases hnear : d≤c+1
    · have htu : t≤4*U := by
        have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hnear
        change t≤(2:ℤ)^(c+1) at hh
        rw [pow_succ,hu] at hh
        nlinarith only [hh]
      have hg : Second R S U (3*D) := second_near U D t hU hD ht hDt
      by_cases hd1 : d=1
      · have ht2 : t=2 := by simp [t,hd1]
        have hf : First R S U 2 D := by
          simpa only [R,S,ht2] using first_two U D hU hD
        exact go 2 D (3*D) (by omega) (by omega) (by omega) (by omega)
          (by omega) hRD (nearSep h D rfl (Or.inl rfl)) hf hg
      · by_cases hd2 : d=2
        · have ht4 : t=4 := by norm_num [t,hd2]
          have hD2 : 2≤D := by omega
          have hf : First R S U 2 (2*D) := by
            simpa only [R,S,ht4] using first_four U D hU hD2
          exact go 2 (2*D) (3*D) (by omega) (by omega) (by omega) (by omega)
            (by omega) hRD (nearSep (h+1) (2*D) (by dsimp [D]; rw [pow_succ]; ring) (Or.inr rfl)) hf hg
        · let q : ℤ := 2^(d-2)
          have hq : 2≤q := by
            change (2:ℤ)^1≤2^(d-2)
            exact pow_le_pow_right₀ (by norm_num) (by omega)
          have htq : t=4*q := by
            calc
              t=(2:ℤ)^((d-2)+2) := by dsimp [t]; congr 1; omega
              _=4*q := by rw [pow_add]; dsimp [q]; norm_num; ring
          have hqU : q≤U := by omega
          have hf : First R S U (3*q) D := by
            simpa only [R,S,htq] using first_near U D q hU hq hqU (by omega)
          have hpS : 3*q≤S := by
            dsimp [S]; rw [htq]
            nlinarith [mul_nonneg (by omega : 0≤q) (by omega : 0≤U-1)]
          exact go (3*q) D (3*D) (by omega) hpS (by omega) (by omega)
            (by omega) hRD (nearSep h D rfl (Or.inl rfl)) hf hg
    · have hfar : c+2≤d := by omega
      have htu : 8*U≤t := by
        have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hfar
        change (2:ℤ)^(c+2)≤t at hh
        rw [pow_add,hu] at hh
        norm_num at hh
        nlinarith only [hh]
      have hg : Second R S U (3*D-1) := second_far U D t hU hDt htu
      by_cases hell : ell=0
      · have hm1 : m=1 := by simp [m,hell]
        have hReq : R=2*U*t := by
          calc
            R=2*U*(2*D) := by dsimp [R]; ring
            _=2*U*t := by rw [hrel,hm1]; ring
        have hf : First R S U (t-1) 2 := by
          rw [hReq]
          exact first_far_one U t hU htu
        have hpS : t-1≤S := by
          dsimp [S]
          nlinarith [mul_nonneg (by omega : 0≤t) (by omega : 0≤U-1)]
        exact go (t-1) 2 (3*D-1) (by omega) hpS (by omega) (by omega)
          (by omega) (by omega) (farSep 1 2 (by norm_num) (by dsimp [h,ell,d] at *; omega)) hf hg
      · have hm2 : 2≤m := by
          change (2:ℤ)^1≤2^ell
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        have hReq : R=2*m*U*t := by
          calc
            R=2*U*(2*D) := by dsimp [R]; ring
            _=2*m*U*t := by rw [hrel]; ring
        have hf : First R S U t m := by
          rw [hReq]
          exact first_far U t m hU ht hm2
        have hpS : t≤S := by
          dsimp [S]
          nlinarith [mul_nonneg (by omega : 0≤t) (by omega : 0≤U-1)]
        exact go t m (3*D-1) (by omega) hpS (by omega) (by omega)
          (by omega) (by omega) (farSep ell m rfl (by dsimp [h,ell,d] at *; omega)) hf hg
  apply realize a b c (by omega) (by omega) hc plan
  simpa only [hr,hs,hu] using hcert

#print axioms actualSource_three_negative_strict_descending_joint_lift

end D5.S3.Combinatorics.Circle.ThreeNegativeStrictDescendingJointLift
