/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/FullCone
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/FullCone
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical mask inventory, exact source totals and coupled prefix seams. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualStrong
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Peak
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.PeakMasks
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.EqualGaps

/-! Physical occurrence partitions, actual source totals and shadow-charge prefix bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.FullCone

open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private mass_margin ceilpos rounded_reserve ceilpos_capacity from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
open private source_shadow_charge two_power_pred from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source
open private seedZ modZ old enlarged charge shadow natural_lift_strips natural_lift_totals natural_lift_strong
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private Strong strong_strips strong_append strong_of_shadow from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Strip
open private label lift_order marked_word from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

open private power_two_ge masked_inventory masked_weighted_masses actual_word_totals
  actual_chain_masses four_reserve_strong
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks

open private actual_masked_strong actual_masked_strong_exact
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualStrong

open private peak_masks peak_word
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.PeakMasks

set_option maxHeartbeats 1000000 in
-- Dyadic valley ratios give a common nonnegative polynomial chart, including its smallest edge.
private theorem valley_rising_bounds (T L P : ℤ) (hT : 4≤T) (hL : 2≤L) (hP : 1≤P) :
    let R:=T*L
    let Z:=2*R*P
    let C:=R*T+R+1
    let A:=R*T*Z+C
    let e1:=2*Z*C
    let e2:=2*(R+1)*Z^2
    let e3:=2*T*Z^2
    e1≤3*A ∧ 3*A≤2*e1-A ∧
    e2≤2*e1*(P+P*L) ∧ 2*e1*(P+P*L)≤2*e2-A ∧
    e3≤2*e1*P ∧ 2*e1*P≤2*e3-A ∧ 2*(P+P*L)<Z := by
  dsimp only
  have ht : 0≤T-4 := by omega
  have hl : 0≤L-2 := by omega
  have hp : 0≤P-1 := by omega
  generalize ht0 : T-4=t at ht
  generalize hl0 : L-2=l at hl
  generalize hp0 : P-1=p at hp
  have heT : T=t+4 := by omega
  have heL : L=l+2 := by omega
  have heP : P=p+1 := by omega
  rw [heT,heL,heP]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | apply sub_nonneg.mp | apply sub_pos.mp
  all_goals ring_nf; positivity


/-- Exact physical masks and all reserves in the rising strict-valley branch. -/
private theorem valley_rising_masks (a b c : ℕ) (hb : 2≤b)
    (hba : b<a) (hac : a<c) :
    let R : ℕ:=2^a
    let T : ℕ:=2^b
    let Z : ℕ:=2^c
    let p:=Z/(2*R)
    let q:=Z/(2*T)
    let C : ℤ:=1+R+R*T
    let A:=seedZ a b c
    let e1:=2*(Z:ℤ)*C
    let e2:=2*((R:ℤ)+1)*(Z:ℤ)^2
    let e3:=2*(T:ℤ)*(Z:ℤ)^2
    3<2^(c+1) ∧ p+q<2^(c-1) ∧
    (∀ e, p.testBit e=true → (p+q).testBit e=true) ∧
    e1≤3*A ∧ 3*A≤2*e1-A ∧
    e2≤2*e1*((p:ℤ)+q) ∧ 2*e1*((p:ℤ)+q)≤2*e2-A ∧
    e3≤2*e1*p ∧ 2*e1*p≤2*e3-A := by
  let R : ℕ:=2^a
  let T : ℕ:=2^b
  let Z : ℕ:=2^c
  let L : ℕ:=2^(a-b)
  let P : ℕ:=2^(c-a-1)
  let p:=Z/(2*R)
  let q:=Z/(2*T)
  let C : ℤ:=1+R+R*T
  let A:=seedZ a b c
  let e1:=2*(Z:ℤ)*C
  let e2:=2*((R:ℤ)+1)*(Z:ℤ)^2
  let e3:=2*(T:ℤ)*(Z:ℤ)^2
  have hR : R=T*L := by
    dsimp [R,T,L]
    rw [←pow_add]
    congr 1
    omega
  have hZ : Z=2*R*P := by
    dsimp [Z,R,P]
    calc
      (2:ℕ)^c=2^((a+1)+(c-a-1)) := by congr 1; omega
      _=2*2^a*2^(c-a-1) := by rw [pow_add,pow_succ]; ring
  have hp : p=P := by
    dsimp only [p]
    rw [hZ,Nat.mul_div_right P (show 0<2*R by dsimp [R]; positivity)]
  have hq : q=P*L := by
    dsimp only [q]
    have he : Z=2*T*(P*L) := by rw [hZ,hR]; ring
    rw [he,Nat.mul_div_right (P*L) (show 0<2*T by dsimp [T]; positivity)]
  have hT4 : 4≤T := by
    dsimp [T]
    exact Nat.pow_le_pow_right Nat.zero_lt_two hb
  have hL2 : 2≤L := by
    dsimp [L]
    exact Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤a-b by omega)
  have hP1 : 1≤P := Nat.one_le_two_pow
  have hri : (R:ℤ)=(T:ℤ)*L := by exact_mod_cast hR
  have hzi : (Z:ℤ)=2*(R:ℤ)*P := by exact_mod_cast hZ
  have hpi : (p:ℤ)=(P:ℤ) := by exact_mod_cast hp
  have hqi : (q:ℤ)=(P:ℤ)*L := by exact_mod_cast hq
  have hA : A=(R:ℤ)*T*Z+(1+R+R*T) := by
    dsimp [A,seedZ,R,T,Z]
  have hrb:=valley_rising_bounds (T:ℤ) (L:ℤ) (P:ℤ)
    (by exact_mod_cast hT4) (by exact_mod_cast hL2) (by exact_mod_cast hP1)
  dsimp only at hrb
  rw [←hri,←hzi] at hrb
  have hC : (R:ℤ)*T+R+1=1+R+R*T := by ring
  rw [hC,←hA,←hqi,←hpi] at hrb
  change e1≤3*A ∧ 3*A≤2*e1-A ∧
    e2≤2*e1*((p:ℤ)+q) ∧ 2*e1*((p:ℤ)+q)≤2*e2-A ∧
    e3≤2*e1*p ∧ 2*e1*p≤2*e3-A ∧ 2*((p:ℤ)+q)<Z at hrb
  obtain ⟨l1,u1,l2,u2,l3,u3,cap⟩:=hrb
  have hzpred : Z=2*2^(c-1) := by
    dsimp [Z]
    calc
      (2:ℕ)^c=2^((c-1)+1) := by congr 1; omega
      _=2*2^(c-1) := by rw [pow_succ]; ring
  have hcap : p+q<2^(c-1) := by
    have h : 2*(p+q)<Z := by exact_mod_cast cap
    rw [hzpred] at h
    omega
  have hucap : 3<2^(c+1) := by
    have h : 4≤2^(c+1) := Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤c+1 by omega)
    omega
  have hqpow : q=2^(c-b-1) := by
    rw [hq]
    dsimp [P,L]
    rw [←pow_add]
    congr 1
    omega
  have hplt : p<2^(c-b-1) := by
    rw [hp]
    dsimp [P]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hor : p ||| q=p+q := by
    rw [hqpow]
    exact Nat.or_two_pow_eq_add_of_lt hplt
  have hbits : ∀ e, p.testBit e=true → (p+q).testBit e=true := by
    intro e he
    rw [←hor,Nat.testBit_or,he]
    simp
  exact ⟨hucap,hcap,hbits,l1,u1,l2,u2,l3,u3⟩

/-- This chamber's actual constructor word contains each physical occurrence once. -/
private theorem valley_rising_inventory (a b c : ℕ) (hb : 2≤b)
    (hba : b<a) (hac : a<c) :
    (baseWord a b c).Perm (List.range (a+b+c+(max (max a b) c+2))) := by
  have hmin : min a c=a := min_eq_left hac.le
  have hnot : ¬(min a c≤b ∧ b≤max a c) := by rw [hmin]; omega
  have hval : b<min a c := by rw [hmin]; exact hba
  have hZR : ¬(2:ℕ)^c≤2^a := not_le.mpr (Nat.pow_lt_pow_right (by decide) hac)
  have hd : max (max a b) c+2=c+2 := by
    rw [max_eq_left hba.le,max_eq_right hac.le]
  let p:=(2:ℕ)^c/(2*2^a)
  let q:=(2:ℕ)^c/(2*2^b)
  have hm:=valley_rising_masks a b c hb hba hac
  have hbits : ∀ e, p.testBit e=true → (p+q).testBit e=true := hm.2.2.1
  dsimp only [baseWord,baseBlocks]
  rw [if_neg hnot]
  simp only [extremaBlocks,if_pos hval,if_neg hZR]
  simp only [hd]
  change (chamberMaskedWord a b c (c+2) 3 0 0 0 (p+q) p 0).Perm _
  apply masked_inventory a b c (c+2) 3 0 0 0 (p+q) p 0
    (by omega) (by omega) (by omega) (by omega)
  · simp
  · simp
  · intro e he _
    simp [Nat.testBit_two_pow_sub_one,he]
  · intro e _ he
    simpa using he
  · intro e _ he
    exact hbits e he
  · simp


set_option maxHeartbeats 1000000 in
/-- The strict rising valley satisfies Strong for its exact physical constructor. -/
private theorem valley_rising_strong (a b c : ℕ) (hb : 2≤b)
    (hba : b<a) (hac : a<c) :
    Strong (old a b c (max (max a b) c+2))
      (charge a b c (max (max a b) c+2))
      (2^(max (max a b) c+2-1)*2^a*2^b*2^c) 0 (seedZ a b c)
      (baseWord a b c) := by
  have hmin : min a c=a := min_eq_left hac.le
  have hnot : ¬(min a c≤b ∧ b≤max a c) := by rw [hmin]; omega
  have hval : b<min a c := by rw [hmin]; exact hba
  have hZR : ¬(2:ℕ)^c≤2^a := not_le.mpr (Nat.pow_lt_pow_right (by decide) hac)
  have hd : max (max a b) c+2=c+2 := by
    rw [max_eq_left hba.le,max_eq_right hac.le]
  let p:=(2:ℕ)^c/(2*2^a)
  let q:=(2:ℕ)^c/(2*2^b)
  obtain ⟨hu,hv,hbit,hs⟩:=valley_rising_masks a b c hb hba hac
  change 3<2^(c+1) at hu
  change p+q<2^(c-1) at hv
  change ∀ e, p.testBit e=true → (p+q).testBit e=true at hbit
  rw [hd]
  dsimp only [baseWord,baseBlocks]
  rw [if_neg hnot]
  simp only [extremaBlocks,if_pos hval,if_neg hZR,hd]
  change Strong (old a b c (c+2)) (charge a b c (c+2))
    (2^(c+2-1)*2^a*2^b*2^c) 0 (seedZ a b c)
    (chamberMaskedWord a b c (c+2) 3 0 0 0 (p+q) p 0)
  apply actual_masked_strong a b c (c+2) 3 0 0 0 (p+q) p 0
    (by omega) hb (by omega) (by omega)
  · simpa only [show c+2-1=c+1 by omega] using hu
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _
  · exact hv
  · exact lt_of_le_of_lt (Nat.le_add_right p q) hv
  · exact Nat.two_pow_pos _
  · simp
  · simp
  · intro e _ he; exact hbit e he
  · simp
  · dsimp only
    have he : (2:ℤ)^(c+2-1)=2*(2:ℤ)^c := by
      rw [show c+2-1=c+1 by omega,pow_succ]; ring
    rw [he]
    simp only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,sub_zero,add_zero,zero_add]
    simp only [p,q,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat] at hs ⊢
    ring_nf at hs ⊢
    exact hs


set_option maxHeartbeats 1000000 in
/-- Polynomial bounds retain the adjacent dyadic ratio at the strict valley's other side. -/
private theorem valley_falling_polynomials (T J L : ℤ)
    (hT : 4≤T) (hJ : 2≤J) (hL : 1≤L) :
    let Z:=T*J; let R:=Z*L; let C:=1+R+R*T
    let A:=R*T*Z+C; let e1:=2*R*C; let e2:=2*R*(R+1)*Z
    let e3:=2*R*T*Z; let u:=4*L-1
    e1≤A*u ∧ A*u≤2*e1-A ∧ A≤A*u ∧
      e3≤2*A ∧ 2*A≤2*e3-A ∧
      (J=2 → e2≤2*A+2*e1 ∧ 2*A+2*e1≤2*e2-A) ∧
      (4≤J → 2*e1≤e2) := by
  have ht : 0≤T-4 := by omega
  have hj : 0≤J-2 := by omega
  have hl : 0≤L-1 := by omega
  generalize ht0 : T-4=t at ht
  generalize hj0 : J-2=j at hj
  generalize hl0 : L-1=l at hl
  have hTe : T=t+4 := by omega
  have hJe : J=j+2 := by omega
  have hLe : L=l+1 := by omega
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hTe,hJe,hLe]; apply sub_nonneg.mp; ring_nf; positivity
  · rw [hTe,hJe,hLe]; apply sub_nonneg.mp; ring_nf; positivity
  · rw [hTe,hJe,hLe]; apply sub_nonneg.mp; ring_nf; positivity
  · rw [hTe,hJe,hLe]; apply sub_nonneg.mp; ring_nf; positivity
  · rw [hTe,hJe,hLe]; apply sub_nonneg.mp; ring_nf; positivity
  · intro he
    rw [he,hTe,hLe]
    constructor <;> apply sub_nonneg.mp <;> ring_nf <;> positivity
  · intro hJ4
    have hj4 : 0≤J-4 := by omega
    generalize hj40 : J-4=j4 at hj4
    have hJ4e : J=j4+4 := by omega
    rw [hJ4e,hTe,hLe]
    apply sub_nonneg.mp
    ring_nf; positivity


set_option maxHeartbeats 1500000 in
/-- All masks and reserves for a strict valley with the first outer gap at least the last. -/
private theorem valley_falling_masks (a b c : ℕ) (hb : 2≤b)
    (hbc : b<c) (hca : c≤a) :
    let R : ℕ:=2^a; let T : ℕ:=2^b; let Z : ℕ:=2^c
    let u:=2*(2*R/Z)-1
    let A:=seedZ a b c
    let e1:=2*(R:ℤ)*(1+(R:ℤ)+(R:ℤ)*T)
    let e2:=2*(R:ℤ)*((R:ℤ)+1)*Z
    let e3:=2*(R:ℤ)*(T:ℤ)*Z
    let uv:=if Z=2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))
    u<2^(a+1) ∧ uv.1<2^(a+1) ∧ uv.2<2^(c-1) ∧
    (∀ e, uv.1.testBit e=true → u.testBit e=true) ∧
    (∀ e, (2:ℕ).testBit e=true → uv.1.testBit e=true) ∧
    e1≤A*u ∧ A*u≤2*e1-A ∧
    e2≤A*uv.1+2*e1*uv.2 ∧ A*uv.1+2*e1*uv.2≤2*e2-A ∧
    e3≤2*A ∧ 2*A≤2*e3-A := by
  let R : ℕ:=2^a
  let T : ℕ:=2^b
  let Z : ℕ:=2^c
  let J : ℕ:=2^(c-b)
  let L : ℕ:=2^(a-c)
  let u:=2*(2*R/Z)-1
  let A:=seedZ a b c
  let e1:=2*(R:ℤ)*(1+(R:ℤ)+(R:ℤ)*T)
  let e2:=2*(R:ℤ)*((R:ℤ)+1)*Z
  let e3:=2*(R:ℤ)*(T:ℤ)*Z
  have hT4 : 4≤T:=Nat.pow_le_pow_right Nat.zero_lt_two hb
  have hJ2 : 2≤J:=Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤c-b by omega)
  have hL1 : 1≤L:=Nat.one_le_two_pow
  have hZ : Z=T*J := by dsimp [Z,T,J]; rw [←pow_add]; congr 1; omega
  have hR : R=Z*L := by dsimp [R,Z,L]; rw [←pow_add]; congr 1; omega
  have hZpos : 0<Z:=Nat.two_pow_pos _
  have hu : u=4*L-1 := by
    have he : 2*R=Z*(2*L) := by rw [hR]; ring
    dsimp [u]
    rw [he,Nat.mul_div_right (2*L) hZpos]
    omega
  have hucast : (u:ℤ)=4*(L:ℤ)-1 := by
    rw [hu,Nat.cast_sub (by omega)]
    push_cast
    ring
  have hfull : u=2^(a-c+2)-1 := by
    rw [hu]
    dsimp [L]
    rw [pow_add]
    norm_num
    omega
  have hcap : u<2^(a+1) := by
    rw [hfull]
    have hp : 2^(a-c+2)≤(2:ℕ)^(a+1) :=
      Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    have : 2^(a-c+2)-1<2^(a-c+2) := Nat.sub_lt (Nat.two_pow_pos _) (by omega)
    omega
  have htwo : ∀ e, (2:ℕ).testBit e=true → u.testBit e=true := by
    intro e he
    have he1 : e=1 := by
      have he' : ((2:ℕ)^1).testBit e=true := he
      have heone : 1=e := by
        simpa only [Nat.testBit_two_pow,decide_eq_true_eq] using he'
      exact heone.symm
    subst e
    rw [hfull]
    simp only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
    omega
  have hri : (R:ℤ)=(Z:ℤ)*L := by exact_mod_cast hR
  have hzi : (Z:ℤ)=(T:ℤ)*J := by exact_mod_cast hZ
  have hp:=valley_falling_polynomials (T:ℤ) (J:ℤ) (L:ℤ)
    (by exact_mod_cast hT4) (by exact_mod_cast hJ2) (by exact_mod_cast hL1)
  dsimp only at hp
  rw [←hzi,←hri,←hucast] at hp
  have hA : A=(R:ℤ)*T*Z+(1+(R:ℤ)+(R:ℤ)*T) := by dsimp [A,seedZ,R,T,Z]
  rw [←hA] at hp
  change e1≤A*u ∧ A*u≤2*e1-A ∧ A≤A*u ∧
    e3≤2*A ∧ 2*A≤2*e3-A ∧
    ((J:ℤ)=2 → e2≤2*A+2*e1 ∧ 2*A+2*e1≤2*e2-A) ∧
    (4≤(J:ℤ) → 2*e1≤e2) at hp
  have h2cap : 2<2^(a+1) := by
    have ht : 4≤2^(a+1) := Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤a+1 by omega)
    omega
  have h1cap : 1<2^(c-1) := by
    have ht : 2≤2^(c-1) := Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤c-1 by omega)
    omega
  change u<2^(a+1) ∧
    (if Z=2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))).1<2^(a+1) ∧
    (if Z=2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))).2<2^(c-1) ∧
    (∀ e, (if Z=2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))).1.testBit e=true →
      u.testBit e=true) ∧
    (∀ e, (2:ℕ).testBit e=true →
      (if Z=2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))).1.testBit e=true) ∧
    e1≤A*u ∧ A*u≤2*e1-A ∧
    e2≤A*(if Z=2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))).1+
      2*e1*(if Z=2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))).2 ∧
    A*(if Z=2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))).1+
      2*e1*(if Z=2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))).2≤2*e2-A ∧
    e3≤2*A ∧ 2*A≤2*e3-A
  by_cases he : Z=2*T
  · simp only [if_pos he]
    have hj : J=2 := by nlinarith [hZ]
    have hbds:=hp.2.2.2.2.2.1 (by exact_mod_cast hj)
    refine ⟨hcap,h2cap,h1cap,htwo,(by intro e he; exact he),hp.1,hp.2.1,?_,?_,hp.2.2.2.1,hp.2.2.2.2.1⟩
    · simpa only [Nat.cast_ofNat,Nat.cast_one,mul_one,mul_comm A 2] using hbds.1
    · simpa only [Nat.cast_ofNat,Nat.cast_one,mul_one,mul_comm A 2] using hbds.2
  · simp only [if_neg he]
    have hJ4 : 4≤J := by
      have hbc2 : 2≤c-b := by
        by_contra hh
        have hj : J=2 := by dsimp [J]; rw [show c-b=1 by omega]; norm_num
        rw [hj] at hZ
        exact he (by omega)
      exact Nat.pow_le_pow_right Nat.zero_lt_two hbc2
    have he1 : 0<e1 := by dsimp [e1]; positivity
    have hApos : 0<A := by dsimp [A,seedZ]; positivity
    have hround:=rounded_reserve A e1 e2 (A*u) hApos he1
      ⟨hp.2.2.1,hp.2.1⟩ (hp.2.2.2.2.2.2 (by exact_mod_cast hJ4))
    let v:=ceilpos (e2-A*u) (2*e1)
    have hvcap : v<2^(c-1) := by
      have hcfull : ((2^(c-1)-1:ℕ):ℤ)=(Z:ℤ)/2-1 := by
        have hzpred : (Z:ℤ)=2*(2:ℤ)^(c-1) := by
          dsimp [Z]; exact two_power_pred c (by omega)
        rw [Nat.cast_sub (Nat.one_le_two_pow)]
        push_cast
        rw [hzpred]
        omega
      apply lt_of_le_of_lt (ceilpos_capacity (e2-A*u) (2*e1) (2^(c-1)-1) (by omega) ?_)
        (Nat.sub_lt (Nat.two_pow_pos _) (by omega))
      rw [hcfull]
      have hm:=mass_margin (R:ℤ) (T:ℤ) (Z:ℤ)
        (power_two_ge a (by omega)) (power_two_ge b hb) (power_two_ge c (by omega))
      have hzhalf : 2*((Z:ℤ)/2)=(Z:ℤ) := by
        have hzpred : (Z:ℤ)=2*(2:ℤ)^(c-1) := by dsimp [Z]; exact two_power_pred c (by omega)
        omega
      have hmult:=mul_pos (show 0<(R:ℤ) by positivity) (show 0<(R:ℤ)*T*Z-2*(1+(R:ℤ)+(R:ℤ)*T) by linarith)
      have hid : 2*e1*((Z:ℤ)/2-1)-(e2-A*u)=
          2*(R:ℤ)*((R:ℤ)*T*Z-2*(1+(R:ℤ)+(R:ℤ)*T))+A*u := by
        dsimp [e1,e2]
        linear_combination 2*(R:ℤ)*(1+(R:ℤ)+(R:ℤ)*T)*hzhalf
      nlinarith only [hid,hmult,hp.2.2.1,hApos]
    exact ⟨hcap,hcap,hvcap,(by intro e he; exact he),htwo,hp.1,hp.2.1,
      hround.1,hround.2,hp.2.2.2.1,hp.2.2.2.2.1⟩


private theorem valley_falling_word (a b c : ℕ) (hb : 2≤b)
    (hbc : b<c) (hca : c≤a) :
    let R : ℕ:=2^a; let T : ℕ:=2^b; let Z : ℕ:=2^c
    let u:=2*(2*R/Z)-1
    let A:=seedZ a b c
    let e1:=2*(R:ℤ)*(1+(R:ℤ)+(R:ℤ)*T)
    let e2:=2*(R:ℤ)*((R:ℤ)+1)*Z
    let uv:=if Z=2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))
    baseWord a b c=chamberMaskedWord a b c (a+2) u uv.1 2 0 uv.2 0 0 := by
  have hmin : min a c=c := min_eq_right hca
  have hnot : ¬(min a c≤b ∧ b≤max a c) := by rw [hmin]; omega
  have hval : b<min a c := by rw [hmin]; exact hbc
  have hZR : (2:ℕ)^c≤2^a := Nat.pow_le_pow_right Nat.zero_lt_two hca
  have hd : max (max a b) c+2=a+2 := by
    rw [max_eq_left (show b≤a by omega),max_eq_left hca]
  have hd4 : (2:ℤ)^(a+2)=4*(2:ℤ)^a := by rw [pow_add]; norm_num; ring
  have hA : (2:ℤ)^a*(2:ℕ)^b*(2:ℕ)^c+(2:ℕ)^a*(2:ℕ)^b+(2:ℕ)^a+1=seedZ a b c := by
    dsimp [seedZ]
    push_cast
    ring
  have he1 : (2:ℤ)^(a+2)*((2:ℕ)^a*(2:ℕ)^b+(2:ℕ)^a+1)/2=
      2*((2:ℕ)^a:ℤ)*(1+((2:ℕ)^a:ℤ)+((2:ℕ)^a:ℤ)*((2:ℕ)^b:ℤ)) := by
    rw [hd4]
    have he : 4*(2:ℤ)^a*((2:ℕ)^a*(2:ℕ)^b+(2:ℕ)^a+1)=
      2*(2*((2:ℕ)^a:ℤ)*(1+((2:ℕ)^a:ℤ)+((2:ℕ)^a:ℤ)*((2:ℕ)^b:ℤ))) := by push_cast; ring
    rw [he]
    omega
  have he2 : (2:ℤ)^(a+2)*(((2:ℕ)^a:ℤ)+1)*(2:ℕ)^c/2=
      2*((2:ℕ)^a:ℤ)*(((2:ℕ)^a:ℤ)+1)*(2:ℕ)^c := by
    rw [hd4]
    have he : 4*(2:ℤ)^a*(((2:ℕ)^a:ℤ)+1)*(2:ℕ)^c=
      2*(2*((2:ℕ)^a:ℤ)*(((2:ℕ)^a:ℤ)+1)*(2:ℕ)^c) := by push_cast; ring
    rw [he]
    omega
  dsimp only [baseWord,baseBlocks]
  rw [if_neg hnot]
  simp only [extremaBlocks,if_pos hval,if_pos hZR,hd]
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hA he1 he2 ⊢
  rw [hA,he1,he2]
  rfl

set_option maxHeartbeats 1000000 in
/-- The other strict-valley half has both complete physical inventory and Strong. -/
private theorem valley_falling_actual (a b c : ℕ) (hb : 2≤b)
    (hbc : b<c) (hca : c≤a) :
    (baseWord a b c).Perm (List.range (a+b+c+(a+2))) ∧
      Strong (old a b c (a+2)) (charge a b c (a+2))
        (2^(a+2-1)*2^a*2^b*2^c) 0 (seedZ a b c) (baseWord a b c) := by
  let R : ℕ:=2^a
  let T : ℕ:=2^b
  let Z : ℕ:=2^c
  let u:=2*(2*R/Z)-1
  let A:=seedZ a b c
  let e1:=2*(R:ℤ)*(1+(R:ℤ)+(R:ℤ)*T)
  let e2:=2*(R:ℤ)*((R:ℤ)+1)*Z
  let uv:=if Z=2*T then (2,1) else (u,ceilpos (e2-A*u) (2*e1))
  obtain ⟨hcap,hcap2,hvcap,hbit12,hbit23,hbounds⟩:=valley_falling_masks a b c hb hbc hca
  change u<2^(a+1) at hcap
  change uv.1<2^(a+1) at hcap2
  change uv.2<2^(c-1) at hvcap
  change e1≤A*u ∧ A*u≤2*e1-A ∧
    e2≤A*uv.1+2*e1*uv.2 ∧ A*uv.1+2*e1*uv.2≤2*e2-A ∧
    2*(R:ℤ)*(T:ℤ)*Z≤2*A ∧ 2*A≤2*(2*(R:ℤ)*(T:ℤ)*Z)-A at hbounds
  have h2cap : 2<2^(a+1) := by
    have ht : 4≤2^(a+1) := Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤a+1 by omega)
    omega
  have hword:=valley_falling_word a b c hb hbc hca
  change baseWord a b c=chamberMaskedWord a b c (a+2) u uv.1 2 0 uv.2 0 0 at hword
  rw [hword]
  constructor
  · apply masked_inventory a b c (a+2) u uv.1 2 0 uv.2 0 0
      (by omega) (by omega) (by omega) (by omega)
    · intro e _ he; exact hbit12 e he
    · intro e _ he; exact hbit23 e he
    · intro e he _; simp [Nat.testBit_two_pow_sub_one,he]
    · intro e _ he; simpa using he
    · simp
    · simp
  · apply actual_masked_strong a b c (a+2) u uv.1 2 0 uv.2 0 0
      (by omega) hb (by omega) (by omega)
    · simpa only [show a+2-1=a+1 by omega] using hcap
    · simpa only [show a+2-1=a+1 by omega] using hcap2
    · simpa only [show a+2-1=a+1 by omega] using h2cap
    · exact Nat.two_pow_pos _
    · exact hvcap
    · exact Nat.two_pow_pos _
    · exact Nat.two_pow_pos _
    · intro e _ he; exact hbit12 e he
    · intro e _ he; exact hbit23 e he
    · simp
    · simp
    · dsimp only
      have he : (2:ℤ)^(a+2-1)=2*(2:ℤ)^a := by
        rw [show a+2-1=a+1 by omega,pow_succ]; ring
      rw [he]
      simp only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,sub_zero,add_zero,zero_add]
      dsimp only [e1,e2,A,R,T,Z] at hbounds
      simp only [Nat.cast_pow,Nat.cast_ofNat] at hbounds
      ring_nf at hbounds ⊢
      exact hbounds


set_option maxHeartbeats 1000000 in
/-- Strong on an actual physical inventory implies both literal cut-zero orders. -/
private theorem actual_orders_of_strong (a b c d : ℕ) (xs : List ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d)
    (hinv : xs.Perm (List.range (a+b+c+d)))
    (hs : Strong (old a b c d) (charge a b c d)
      (2^(d-1)*2^a*2^b*2^c) 0 (seedZ a b c) xs) :
    let k:=a+b+c+d
    let seed:=1+2^a+2^(a+b)+2^(a+b+c)
    let sigma:=xs.map (label k (by omega))
    OriginalOrder k seed sigma ∧
      OriginalOrder (k+1) (2*seed) (earWord k sigma 0) := by
  let k:=a+b+c+d
  let seed:=1+2^a+2^(a+b)+2^(a+b+c)
  let A:=seedZ a b c
  let B:ℤ:=2^(d-1)*2^a*2^b*2^c
  let N:=modZ a b c d
  have hseed : (seed:ℤ)=A := by
    dsimp [seed,A,seedZ]
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,pow_add]
    ring
  have hmod : modulus k=N := by dsimp [modulus,k,N,modZ]; simp only [pow_add]
  have hmod' : modulus (k+1)=2*N+1 := by
    dsimp [modulus]
    rw [pow_succ,←hmod]
    dsimp [modulus]
    ring
  have hNB : N=2*B-1 := by
    dsimp [N,modZ,B]
    rw [two_power_pred d (by omega)]
    ring
  have hB : 1≤B := by
    have hp : 0<B := by dsimp [B]; positivity
    omega
  have hstrips:=strong_strips (old a b c d) (charge a b c d) B 0 A xs hs
  have hfuns : (fun i => 2*old a b c d i-charge a b c d i)=enlarged a b c d := by
    funext i; dsimp [charge]; ring
  rw [hfuns] at hstrips
  simp only [mul_zero,zero_add] at hstrips
  have hold : OriginalOrder k seed (xs.map (label k (by omega))) := by
    apply lift_order k seed (by dsimp [k]; omega) xs hinv
    · have hsOld : InStrip (fun i => centered N (2^i*A)) (B-1) 0 xs := hstrips.1
      simpa only [hmod,hseed,show N/2=B-1 by omega] using hsOld
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k seed (by dsimp [k];omega)
  have hear:=(source_shadow_charge a b c d ha hb hc hd).2.2.2.2
  change enlarged a b c d (d+c+b+a)=A at hear
  rw [show d+c+b+a=k by dsimp [k]; omega] at hear
  have hnewstrip : InStrip (enlarged a b c d) N 0 ([k]++xs) := by
    change 0≤0 ∧ 0≤N ∧ InStrip (enlarged a b c d) N (0+enlarged a b c d k) xs
    exact ⟨by omega,by omega,by simpa only [hear,zero_add,hNB] using hstrips.2⟩
  have hnewperm : ([k]++xs).Perm (List.range (k+1)) := by
    have hp:=(List.perm_append_singleton k xs).symm
    have hr : List.range k++[k]=List.range (k+1) := by
      simpa only [Nat.succ_eq_add_one] using (List.range_succ (n:=k)).symm
    exact hp.trans ((hinv.append_right [k]).trans (List.Perm.of_eq hr))
  have hnew : OriginalOrder (k+1) (2*seed)
      (([k]++xs).map (label (k+1) (by omega))) := by
    apply lift_order (k+1) (2*seed) (by omega) ([k]++xs) hnewperm
    · have hhalf : (2*N+1)/2=N := by omega
      have hsNew : InStrip (fun i => centered (2*N+1) (2^i*(2*A))) N 0 ([k]++xs) :=
        hnewstrip
      simpa only [hmod,hmod',Nat.cast_mul,Nat.cast_ofNat,hseed,hhalf] using hsNew
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*seed) (by dsimp [k];omega)
  refine ⟨hold,?_⟩
  rw [show earWord k (xs.map (label k (by omega))) 0=
      ([k]++xs).map (label (k+1) (by omega)) by
    simpa using marked_word k 0 (by dsimp [k];omega) [] xs rfl hinv]
  exact hnew

set_option maxHeartbeats 1000000 in
/-- Every natural lift of the rising valley uses the same old physical word and literal ear. -/
private theorem valley_rising_orders (a b c d : ℕ)
    (hb : 2≤b) (hba : b<a) (hac : a<c) (hd : c+2≤d) :
    let k:=a+b+c+d
    let seed:=1+2^a+2^(a+b)+2^(a+b+c)
    let sigma:=(physicalWord a b c d).map (label k (by omega))
    OriginalOrder k seed sigma ∧
      OriginalOrder (k+1) (2*seed) (earWord k sigma 0) := by
  let d0:=c+2
  let t:=d-d0
  let B:ℤ:=2^(d0-1)*2^a*2^b*2^c
  let xs:=baseWord a b c
  have hd0 : max (max a b) c+2=d0 := by
    dsimp [d0]; rw [max_eq_left hba.le,max_eq_right hac.le]
  have hd' : d0+t=d := by dsimp [d0,t] at *; omega
  have hinv : xs.Perm (List.range (a+b+c+d0)) := by
    simpa only [hd0] using valley_rising_inventory a b c hb hba hac
  have hstrong : Strong (old a b c d0) (charge a b c d0) B 0 (seedZ a b c) xs := by
    simpa only [hd0] using valley_rising_strong a b c hb hba hac
  have hx : ∀ i∈xs, i<a+b+c+d0 := fun i hi => List.mem_range.mp (hinv.mem_iff.mp hi)
  have hAB : seedZ a b c≤B := by
    cases he:xs with
    | nil => simp only [he,Strong,zero_add] at hstrong; exact hstrong.2.2.2
    | cons i ys => simp only [he,Strong,zero_add] at hstrong; exact hstrong.2.2.2.1
  have hA : 1≤seedZ a b c := by
    have hp : 0<seedZ a b c := by dsimp [seedZ]; positivity
    omega
  have htot:=actual_word_totals a b c d0 xs (by omega) hb (by omega) (by dsimp [d0];omega) hinv
  have hl:=natural_lift_strong a b c d0 t B xs (by omega) hb (by omega)
    (by dsimp [d0];omega) hA hAB hx hstrong htot.2
  have hpow : (2:ℤ)^t*B=2^(d-1)*2^a*2^b*2^c := by
    dsimp [B]
    rw [show d-1=t+(d0-1) by dsimp [t,d0] at *;omega,pow_add]
    ring
  rw [hd',hpow] at hl
  have hword : physicalWord a b c d=List.range t++xs.map (t+·) := by
    dsimp [physicalWord,t,xs]
    rw [hd0]
  have hlInv : (List.range t++xs.map (t+·)).Perm (List.range (a+b+c+d)) := by
    have hmap : (List.range (a+b+c+d0)).map (t+·)=List.range' t (a+b+c+d0) := by
      rw [List.range_eq_range']
      simpa only [Nat.add_zero] using (List.map_add_range' (a:=t) 0 (a+b+c+d0) 1)
    have hi:=(hinv.map (t+·)).append_left (List.range t)
    have hr := List.range'_append_1 (s:=0) (m:=t) (n:=a+b+c+d0)
    simp only [Nat.zero_add] at hr
    rw [hmap,List.range_eq_range',hr] at hi
    simpa only [Nat.zero_add,←List.range_eq_range',show t+(a+b+c+d0)=a+b+c+d by omega] using hi
  apply actual_orders_of_strong a b c d (physicalWord a b c d) (by omega) hb (by omega) (by omega)
  · simpa only [hword] using hlInv
  · simpa only [hword] using hl


set_option maxHeartbeats 1000000 in
-- The exact peak masks satisfy the common actual-source Strong criterion.
private theorem peak_actual (a b c : ℕ) (ha : 2≤a) (hc : 2≤c)
    (hab : a<b) (hcb : c<b) :
    (baseWord a b c).Perm (List.range (a+b+c+(b+2))) ∧
      Strong (old a b c (b+2)) (charge a b c (b+2))
        (2^(b+2-1)*2^a*2^b*2^c) 0 (seedZ a b c) (baseWord a b c) := by
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
  have hm:=peak_masks a b c ha hc hab hcb
  change uv.1<2^(b+1) ∧ s<2^(b+1) ∧ uw.1<2^(b+1) ∧
    uv.2<2^(c-1) ∧ uw.2<2^(b-1) ∧
    (∀ e, s.testBit e=true → uv.1.testBit e=true) ∧
    (∀ e, uw.1.testBit e=true → s.testBit e=true) ∧
    e1≤A*uv.1-2*e1*uv.2 ∧ A*uv.1-2*e1*uv.2≤2*e1-A ∧
    e2≤A*s ∧ A*s≤2*e2-A ∧
    e3≤A*uw.1+2*e2*uw.2 ∧ A*uw.1+2*e2*uw.2≤2*e3-A at hm
  obtain ⟨hu1,hu2,hu3,hv0,hw,h12,h23,hres⟩:=hm
  have hword:=peak_word a b c hab hcb
  change baseWord a b c=chamberMaskedWord a b c (b+2) uv.1 s uw.1 uv.2 0 0 uw.2 at hword
  rw [hword]
  constructor
  · apply masked_inventory a b c (b+2) uv.1 s uw.1 uv.2 0 0 uw.2
      (by omega) (by omega) (by omega) (by omega)
    · intro e _ he; exact h12 e he
    · intro e _ he; exact h23 e he
    · intro e he _; simp [Nat.testBit_two_pow_sub_one,he]
    · intro e _ he; simp at he
    · simp
    · simp
  · apply actual_masked_strong a b c (b+2) uv.1 s uw.1 uv.2 0 0 uw.2
      ha (by omega) hc (by omega)
    · simpa only [show b+2-1=b+1 by omega] using hu1
    · simpa only [show b+2-1=b+1 by omega] using hu2
    · simpa only [show b+2-1=b+1 by omega] using hu3
    · exact hv0
    · exact Nat.two_pow_pos _
    · exact Nat.two_pow_pos _
    · exact hw
    · intro e _ he; exact h12 e he
    · intro e _ he; exact h23 e he
    · simp
    · simp
    · dsimp only
      have he : (2:ℤ)^(b+2-1)=2*(2:ℤ)^b := by
        rw [show b+2-1=b+1 by omega,pow_succ]; ring
      rw [he]
      simp only [Nat.cast_zero,mul_zero,add_zero]
      dsimp only [A,e1,e2,e3,R,T,Z] at hres
      simp only [Nat.cast_pow,Nat.cast_ofNat] at hres
      ring_nf at hres ⊢
      exact hres

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.FullCone
