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
open private mass_margin ceilpos from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
open private source_shadow_charge two_power_pred from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source
open private seedZ modZ old enlarged charge shadow natural_lift_strips natural_lift_totals
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private Strong strong_strips strong_append strong_of_shadow from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Strip
open private label lift_order marked_word from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

open private power_two_ge masked_inventory masked_weighted_masses actual_word_totals
  actual_chain_masses four_reserve_strong
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks

set_option maxHeartbeats 1600000 in
/-- The reserve inequalities are realized by the actual physical centered sources. -/
private theorem actual_masked_strong
    (a b c d u1 u2 u3 v0 v2 v3 w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d)
    (hu1 : u1<2^(d-1)) (hu2 : u2<2^(d-1)) (hu3 : u3<2^(d-1))
    (hv0 : v0<2^(c-1)) (hv2 : v2<2^(c-1)) (hv3 : v3<2^(c-1))
    (hw : w<2^(b-1))
    (hU12 : ∀ e<d-1, u2.testBit e=true → u1.testBit e=true)
    (hU23 : ∀ e<d-1, u3.testBit e=true → u2.testBit e=true)
    (hV23 : ∀ e<c-1, v3.testBit e=true → v2.testBit e=true)
    (hVxor : (v0 ||| v2) ^^^ v2=v0)
    (hs : let R : ℤ:=2^a; let T : ℤ:=2^b; let Z : ℤ:=2^c
      let H : ℤ:=2^(d-1); let A:=seedZ a b c
      let e1:=H*(1+R+R*T); let e2:=H*(R+1)*Z; let e3:=H*T*Z
      let S1:=A*u1-2*e1*v0; let S2:=A*u2+2*e1*v2
      let S3:=A*u3+2*e1*v3+2*e2*w
      e1≤S1 ∧ S1≤2*e1-A ∧ e2≤S2 ∧ S2≤2*e2-A ∧
        e3≤S3 ∧ S3≤2*e3-A) :
    Strong (old a b c d) (charge a b c d)
      (2^(d-1)*2^a*2^b*2^c) 0 (seedZ a b c)
      (chamberMaskedWord a b c d u1 u2 u3 v0 v2 v3 w) := by
  let R : ℤ:=2^a
  let T : ℤ:=2^b
  let Z : ℤ:=2^c
  let H : ℤ:=2^(d-1)
  let A:=seedZ a b c
  let B:=H*R*T*Z
  let e1:=H*(1+R+R*T)
  let e2:=H*(R+1)*Z
  let e3:=H*T*Z
  let f:=old a b c d
  let q:=charge a b c d
  let z:=shadow a b c d
  let P:=maskedBlocks a b c d u1 u2 u3 v0 v2 v3 w
  let S1:=A*u1-2*e1*v0
  let S2:=A*u2+2*e1*v2
  let S3:=A*u3+2*e1*v3+2*e2*w
  change e1≤S1 ∧ S1≤2*e1-A ∧ e2≤S2 ∧ S2≤2*e2-A ∧
    e3≤S3 ∧ S3≤2*e3-A at hs
  have hR : 4≤R:=power_two_ge a ha
  have hT : 4≤T:=power_two_ge b hb
  have hZ : 4≤Z:=power_two_ge c hc
  have hH : 1≤H:=one_le_pow₀ (by norm_num)
  have hA : 1≤A := by
    have hp : 0<A := by dsimp [A,seedZ]; positivity
    omega
  have hB : 1≤B := by
    have hp : 0<B := by dsimp [B]; positivity
    omega
  have hshadow : (fun i => f i-q i)=z := by
    funext i
    dsimp [f,q,z,charge,shadow]
    ring
  have hdecomp (i : ℕ) : f i=z i+q i := by
    have h:=congrFun hshadow i
    linarith only [h]
  obtain ⟨u,v,ww,x,_⟩:=source_shadow_charge a b c d ha hb hc hd
  change (∀ i<d, q i=(if i+1<d then 0 else 1) ∧
    z i=(if i+1<d then 2^i*A else -B+e1)) at u
  change (∀ i<c, q (d+i)=(if i+1<c then 2^i else 2^(c-1)+1) ∧
    z (d+i)=(if i+1<c then 2^i*(2*e1) else -B+e2)) at v
  change (∀ i<b, q (d+c+i)=(if i+1<b then 2^i*(Z+1) else 2^(b-1)*(Z+1)+1) ∧
    z (d+c+i)=(if i+1<b then 2^i*(2*e2) else -B+e3)) at ww
  change (∀ i<a, q (d+c+b+i)=(if i+1<a then 2^i*(T*Z+T+1) else 2^(a-1)*(T*Z+T+1)+1) ∧
    z (d+c+b+i)=(if i+1<a then 2^i*(2*e3) else -B)) at x
  have hzU (e : ℕ) (he : e<d-1) : z (0+e)=2^e*A := by
    simpa only [if_pos (show e+1<d by omega),Nat.zero_add] using (u e (by omega)).2
  have hzV (e : ℕ) (he : e<c-1) : z (d+e)=2^e*(2*e1) := by
    simpa only [if_pos (show e+1<c by omega)] using (v e (by omega)).2
  have hzW (e : ℕ) (he : e<b-1) : z (d+c+e)=2^e*(2*e2) := by
    simpa only [if_pos (show e+1<b by omega)] using (ww e (by omega)).2
  have good (i : ℕ) (hq : 0≤q i) (hz : 0≤z i) :
      0≤f i ∧ 0≤q i ∧ 0≤f i-q i := by
    rw [hdecomp]
    exact ⟨by omega,hq,by omega⟩
  have goodU (mask i : ℕ) (hi : i∈labels (d-1) 0 mask) :
      0≤f i ∧ 0≤q i ∧ 0≤f i-q i := by
    obtain ⟨e,he,_,rfl⟩:=(labels_mem _ _ _ _).mp hi
    have ht:=u e (by omega)
    simp only [if_pos (show e+1<d by omega),Nat.zero_add] at ht ⊢
    apply good
    · rw [ht.1]
    · rw [ht.2]; positivity
  have goodV (mask i : ℕ) (hi : i∈labels (c-1) d mask) :
      0≤f i ∧ 0≤q i ∧ 0≤f i-q i := by
    obtain ⟨e,he,_,rfl⟩:=(labels_mem _ _ _ _).mp hi
    have ht:=v e (by omega)
    simp only [if_pos (show e+1<c by omega)] at ht
    apply good
    · rw [ht.1]; positivity
    · rw [ht.2]; dsimp [e1]; positivity
  have goodW (mask i : ℕ) (hi : i∈labels (b-1) (d+c) mask) :
      0≤f i ∧ 0≤q i ∧ 0≤f i-q i := by
    obtain ⟨e,he,_,rfl⟩:=(labels_mem _ _ _ _).mp hi
    have ht:=ww e (by omega)
    simp only [if_pos (show e+1<b by omega)] at ht
    apply good
    · rw [ht.1]; positivity
    · rw [ht.2]; dsimp [e2]; positivity
  have goodX (mask i : ℕ) (hi : i∈labels (a-1) (d+c+b) mask) :
      0≤f i ∧ 0≤q i ∧ 0≤f i-q i := by
    obtain ⟨e,he,_,rfl⟩:=(labels_mem _ _ _ _).mp hi
    have ht:=x e (by omega)
    simp only [if_pos (show e+1<a by omega)] at ht
    apply good
    · rw [ht.1]; positivity
    · rw [ht.2]; dsimp [e3]; positivity
  have hp1 : ∀ i∈P.first, 0≤f i ∧ 0≤q i ∧ 0≤f i-q i := by
    intro i hi
    rcases List.mem_append.mp hi with h|h
    · exact goodU _ _ h
    · exact goodV _ _ h
  have hp2 : ∀ i∈P.second, 0≤f i ∧ 0≤q i ∧ 0≤f i-q i := by
    intro i hi
    rcases List.mem_append.mp hi with h|h
    · exact goodU _ _ h
    · exact goodV _ _ h
  have hp3 : ∀ i∈P.third, 0≤f i ∧ 0≤q i ∧ 0≤f i-q i := by
    intro i hi
    rcases List.mem_append.mp hi with h|h
    · rcases List.mem_append.mp h with h|h
      · exact goodU _ _ h
      · exact goodV _ _ h
    · exact goodW _ _ h
  have hp4 : ∀ i∈P.fourth, 0≤f i ∧ 0≤q i ∧ 0≤f i-q i := by
    intro i hi
    rcases List.mem_append.mp hi with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact goodU _ _ h
        · exact goodV _ _ h
      · exact goodW _ _ h
    · exact goodX _ _ h
  have n1:=u (d-1) (by omega)
  have n2:=v (c-1) (by omega)
  have n3:=ww (b-1) (by omega)
  have n4:=x (a-1) (by omega)
  simp only [if_neg (show ¬d-1+1<d by omega),if_neg (show ¬c-1+1<c by omega),
    if_neg (show ¬b-1+1<b by omega),if_neg (show ¬a-1+1<a by omega)] at n1 n2 n3 n4
  rw [show d+(c-1)=d+c-1 by omega] at n2
  rw [show d+c+(b-1)=d+c+b-1 by omega] at n3
  rw [show d+c+b+(a-1)=d+c+b+a-1 by omega] at n4
  have hn1 : 1≤q (d-1) := by rw [n1.1]
  have hn2 : 1≤q (d+c-1) := by
    rw [n2.1]
    have hp : (0:ℤ)≤2^(c-1) := by positivity
    omega
  have hn3 : 1≤q (d+c+b-1) := by
    rw [n3.1]
    have hp : (0:ℤ)≤2^(b-1)*(Z+1) := by positivity
    omega
  have hn4 : 1≤q (d+c+b+a-1) := by
    rw [n4.1]
    have hp : (0:ℤ)≤2^(a-1)*(T*Z+T+1) := by positivity
    omega
  have mass:=actual_chain_masses a b c d ha hb hc hd
  change _=B+e1-A ∧ _=B+e2-2*e1 ∧ _=B+e3-2*e2 ∧ _=B-2*e3 at mass
  have hm:=masked_weighted_masses a b c d u1 u2 u3 v0 v2 v3 w z
    A (2*e1) (2*e2) (B+e1-A) (B+e2-2*e1) (B+e3-2*e2) (B-2*e3)
    hu1 hu2 hu3 hv0 hv2 hv3 hw hU12 hU23 hV23 hVxor hzU hzV hzW
    mass.1 mass.2.1 mass.2.2.1 mass.2.2.2
  change (P.first.map z).sum=B+e1-A-S1 ∧
    (P.second.map z).sum=B+e2-2*e1+S1-S2 ∧
    (P.third.map z).sum=B+e3-2*e2+S2-S3 ∧
    (P.fourth.map z).sum=B-2*e3+S3 at hm
  have inv:=masked_inventory a b c d u1 u2 u3 v0 v2 v3 w
    (by omega) (by omega) (by omega) (by omega) hU12 hU23
    (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
    (by intro e _ he; simp only [Nat.testBit_or,he,Bool.or_true]) hV23 hVxor
  have tot:=actual_word_totals a b c d _ ha hb hc hd inv
  have hqsum (xs : List ℕ) (hp : ∀ i∈xs, 0≤f i ∧ 0≤q i ∧ 0≤f i-q i) :
      0≤(xs.map q).sum := List.sum_nonneg (by
    intro v hv; obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hv; exact (hp i hi).2.1)
  have eq1 : e1≤B := by
    have hh:=mass_margin R T Z hR hT hZ
    have hC : 0≤1+R+R*T := by positivity
    have h:=mul_le_mul_of_nonneg_left (show 1+R+R*T≤R*T*Z by linarith only [hh,hC]) (show 0≤H by omega)
    dsimp [e1,B]; nlinarith only [h]
  have eq2 : e2≤B := by
    have h:=mul_nonneg (show 0≤R*T-(R+1) by nlinarith only [hR,hT]) (show 0≤H*Z by positivity)
    dsimp [e2,B]; nlinarith only [h]
  have eq3 : e3≤B := by
    have h:=mul_nonneg (show 0≤R-1 by omega) (show 0≤H*T*Z by positivity)
    dsimp [e3,B]; nlinarith only [h]
  change Strong f q B 0 A _
  apply four_reserve_strong f q B A e1 e2 e3 S1 S2 S3
    P.first P.second P.third P.fourth (d-1) (d+c-1) (d+c+b-1) (d+c+b+a-1)
    hB hA hp1 hp2 hp3 hp4 hn1 hn2 hn3 hn4 eq1 eq2 eq3
  · simpa only [←hshadow] using n1.2
  · simpa only [←hshadow] using n2.2
  · simpa only [←hshadow] using n3.2
  · simpa only [←hshadow] using n4.2
  · simpa only [hshadow] using hm.1
  · simpa only [hshadow] using hm.2.1
  · simpa only [hshadow] using hm.2.2.1
  · simpa only [hshadow] using hm.2.2.2
  · exact ⟨hs.1,by linarith [hqsum P.first hp1]⟩
  · exact ⟨hs.2.2.1,by linarith [hqsum P.first hp1,hqsum P.second hp2]⟩
  · exact ⟨hs.2.2.2.2.1,by linarith [hqsum P.first hp1,hqsum P.second hp2,hqsum P.third hp3]⟩
  · exact tot.1
  · exact tot.2


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
  · omega
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
    dsimp only at hs
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat] at hs
    ring_nf at hs ⊢
    exact hs

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.FullCone
