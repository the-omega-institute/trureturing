/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/FullCone
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/FullCone
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical mask inventory, exact source totals and coupled prefix seams. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Peak
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.EqualGaps

/-! Physical occurrence partitions, actual source totals and shadow-charge prefix bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.FullCone

open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private ceilpos from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
open private source_shadow_charge two_power_pred from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source
open private seedZ modZ old enlarged charge shadow natural_lift_strips natural_lift_totals
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private Strong strong_strips strong_append strong_of_shadow from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Strip
open private label lift_order marked_word from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

open private power_two_ge masked_inventory masked_weighted_masses actual_word_totals
  actual_chain_masses four_reserve_strong
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks

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

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.FullCone
