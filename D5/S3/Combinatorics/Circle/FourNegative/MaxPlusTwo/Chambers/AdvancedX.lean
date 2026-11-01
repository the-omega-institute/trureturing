/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/AdvancedX
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/AdvancedX
   mirror-E: none(waiver:internal-source-bridge)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact physical source criterion when X-positive labels advance before the third negative. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualStrong
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.DescendingMasks

/-! Advancing X changes the third reserve and the remaining charge together. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open SourceWidth PeriodicShortening RunFirstEarTransport
open private mass_margin from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
open private source_shadow_charge from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source
open private seedZ old charge shadow from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private Strong from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Strip
open private power_two_ge masked_inventory masked_weighted_masses actual_word_totals actual_chain_masses four_reserve_strong
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
open private masked_remaining_charges from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ExactCharges

private def advancedBlocks (a b c d u1 u2 u3 v0 v2 v3 w xt : ℕ) : Blocks :=
  let P:=maskedBlocks a b c d u1 u2 u3 v0 v2 v3 w
  let X:=labels (a-1) (d+c+b)
  ⟨P.first,P.second,P.third++X xt,
    labels (d-1) 0 u3++labels (c-1) d v3++labels (b-1) (d+c) w++X (2^(a-1)-1 ^^^ xt)⟩
private def advancedWord (a b c d u1 u2 u3 v0 v2 v3 w xt : ℕ) : List ℕ :=
  (advancedBlocks a b c d u1 u2 u3 v0 v2 v3 w xt).word a b c d

private theorem advanced_permutation (a b c d u1 u2 u3 v0 v2 v3 w xt : ℕ) :
    (advancedWord a b c d u1 u2 u3 v0 v2 v3 w xt).Perm
      (chamberMaskedWord a b c d u1 u2 u3 v0 v2 v3 w) := by
  let P0:=maskedBlocks a b c d u1 u2 u3 v0 v2 v3 w
  let X:=labels (a-1) (d+c+b)
  let xf:=2^(a-1)-1
  have hxpart : (X (xf ^^^ xt)++X xt).Perm (X xf) :=
    chamberLabels_split (a-1) (d+c+b) xf xt
      (by intro e he _; simp [xf,Nat.testBit_two_pow_sub_one,he])
  apply Multiset.coe_eq_coe.mp
  have hxms:=Multiset.coe_eq_coe.mpr hxpart
  simp only [←Multiset.coe_add] at hxms
  change (↑(P0.first++[d-1]++P0.second++[d+c-1]++(P0.third++X xt)++
    [d+c+b-1]++(labels (d-1) 0 u3++labels (c-1) d v3++
      labels (b-1) (d+c) w++X (xf ^^^ xt))++[d+c+b+a-1]) : Multiset ℕ)=
    ↑(P0.first++[d-1]++P0.second++[d+c-1]++P0.third++[d+c+b-1]++
      (labels (d-1) 0 u3++labels (c-1) d v3++labels (b-1) (d+c) w++X xf)++[d+c+b+a-1])
  simp only [←Multiset.coe_add]
  rw [←hxms]
  ac_rfl

set_option maxHeartbeats 1600000 in
/-- The reserve inequalities are realized by the actual physical centered sources. -/
private theorem actual_advanced_strong_exact
    (a b c d u1 u2 u3 v0 v2 v3 w xt : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d)
    (hu1 : u1<2^(d-1)) (hu2 : u2<2^(d-1)) (hu3 : u3<2^(d-1))
    (hv0 : v0<2^(c-1)) (hv2 : v2<2^(c-1)) (hv3 : v3<2^(c-1))
    (hw : w<2^(b-1)) (hxt : xt<2^(a-1))
    (hU12 : ∀ e<d-1, u2.testBit e=true → u1.testBit e=true)
    (hU23 : ∀ e<d-1, u3.testBit e=true → u2.testBit e=true)
    (hV23 : ∀ e<c-1, v3.testBit e=true → v2.testBit e=true)
    (hVxor : (v0 ||| v2) ^^^ v2=v0)
    (hs : let R : ℤ:=2^a; let T : ℤ:=2^b; let Z : ℤ:=2^c
      let H : ℤ:=2^(d-1); let A:=seedZ a b c
      let e1:=H*(1+R+R*T); let e2:=H*(R+1)*Z; let e3:=H*T*Z
      let S1:=A*u1-2*e1*v0; let S2:=A*u2+2*e1*v2
      let S3:=A*u3+2*e1*v3+2*e2*w-2*e3*xt
      e1≤S1 ∧ S1≤2*e1-(A-1-v0) ∧ e2≤S2 ∧ S2≤2*e2-(A-Z-1+v2) ∧
        e3≤S3 ∧ S3≤2*e3-(A-(T*Z+T+1)+v3+(Z+1)*w-(T*Z+T+1)*xt)) :
    Strong (old a b c d) (charge a b c d)
      (2^(d-1)*2^a*2^b*2^c) 0 (seedZ a b c)
      (advancedWord a b c d u1 u2 u3 v0 v2 v3 w xt) := by
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
  let P0:=maskedBlocks a b c d u1 u2 u3 v0 v2 v3 w
  let P:=advancedBlocks a b c d u1 u2 u3 v0 v2 v3 w xt
  let X:=labels (a-1) (d+c+b)
  let xf:=2^(a-1)-1
  let S1:=A*u1-2*e1*v0
  let S2:=A*u2+2*e1*v2
  let S0:=A*u3+2*e1*v3+2*e2*w
  let S3:=S0-2*e3*xt
  change e1≤S1 ∧ S1≤2*e1-(A-1-v0) ∧ e2≤S2 ∧ S2≤2*e2-(A-Z-1+v2) ∧
    e3≤S3 ∧ S3≤2*e3-(A-(T*Z+T+1)+v3+(Z+1)*w-(T*Z+T+1)*xt) at hs
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
    rcases List.mem_append.mp hi with hi|hi
    · rcases List.mem_append.mp hi with h|h
      · rcases List.mem_append.mp h with h|h
        · exact goodU _ _ h
        · exact goodV _ _ h
      · exact goodW _ _ h
    · exact goodX _ _ hi
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
  have hzX (e : ℕ) (he : e<a-1) : z (d+c+b+e)=2^e*(2*e3) := by
    simpa only [if_pos (show e+1<a by omega)] using (x e (by omega)).2
  have hqX (e : ℕ) (he : e<a-1) : q (d+c+b+e)=2^e*(T*Z+T+1) := by
    simpa only [if_pos (show e+1<a by omega)] using (x e (by omega)).1
  have hxz : ((X xt).map z).sum=(xt:ℤ)*(2*e3) :=
    chamberLabels_sum (a-1) (d+c+b) xt hxt z (2*e3) hzX
  have hxq : ((X xt).map q).sum=(xt:ℤ)*(T*Z+T+1) :=
    chamberLabels_sum (a-1) (d+c+b) xt hxt q (T*Z+T+1) hqX
  have hxpart : (X (xf ^^^ xt)++X xt).Perm (X xf) :=
    chamberLabels_split (a-1) (d+c+b) xf xt
      (by intro e he _; simp [xf,Nat.testBit_two_pow_sub_one,he])
  have hxzm:=((hxpart.map z).sum_eq)
  simp only [List.map_append,List.sum_append] at hxzm
  have hm0:=masked_weighted_masses a b c d u1 u2 u3 v0 v2 v3 w z
    A (2*e1) (2*e2) (B+e1-A) (B+e2-2*e1) (B+e3-2*e2) (B-2*e3)
    hu1 hu2 hu3 hv0 hv2 hv3 hw hU12 hU23 hV23 hVxor hzU hzV hzW
    mass.1 mass.2.1 mass.2.2.1 mass.2.2.2
  change (P0.first.map z).sum=B+e1-A-S1 ∧
    (P0.second.map z).sum=B+e2-2*e1+S1-S2 ∧
    (P0.third.map z).sum=B+e3-2*e2+S2-S0 ∧
    (P0.fourth.map z).sum=B-2*e3+S0 at hm0
  have hm : (P.first.map z).sum=B+e1-A-S1 ∧
      (P.second.map z).sum=B+e2-2*e1+S1-S2 ∧
      (P.third.map z).sum=B+e3-2*e2+S2-S3 ∧
      (P.fourth.map z).sum=B-2*e3+S3 := by
    refine ⟨hm0.1,hm0.2.1,?_,?_⟩
    · change ((P0.third++X xt).map z).sum=_
      rw [List.map_append,List.sum_append,hm0.2.2.1,hxz]
      dsimp [S3]; ring
    · have hh : (P.fourth.map z).sum+((X xt).map z).sum=(P0.fourth.map z).sum := by
        dsimp only [P,P0,advancedBlocks,maskedBlocks]
        simp only [List.map_append,List.sum_append]
        dsimp only [X,xf] at hxzm
        linarith only [hxzm]
      rw [hxz,hm0.2.2.2] at hh
      dsimp [S3]
      linarith only [hh]
  have inv0:=masked_inventory a b c d u1 u2 u3 v0 v2 v3 w
    (by omega) (by omega) (by omega) (by omega) hU12 hU23
    (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
    (by intro e _ he; simp only [Nat.testBit_or,he,Bool.or_true]) hV23 hVxor
  have hpword:=advanced_permutation a b c d u1 u2 u3 v0 v2 v3 w xt
  have inv:=hpword.trans inv0
  have tot:=actual_word_totals a b c d _ ha hb hc hd inv
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
  have hc0:=masked_remaining_charges a b c d u1 u2 u3 v0 v2 v3 w
    ha hb hc hd hu1 hu2 hu3 hv0 hv2 hv3 hw hU12 hU23 hV23 hVxor
  change A-(P0.first.map q).sum-q (d-1)=A-1-v0 ∧
    A-(P0.first.map q).sum-q (d-1)-(P0.second.map q).sum-q (d+c-1)=A-Z-1+v2 ∧
    A-(P0.first.map q).sum-q (d-1)-(P0.second.map q).sum-q (d+c-1)-
      (P0.third.map q).sum-q (d+c+b-1)=A-(T*Z+T+1)+v3+(Z+1)*w at hc0
  have hcharges : A-(P.first.map q).sum-q (d-1)=A-1-v0 ∧
      A-(P.first.map q).sum-q (d-1)-(P.second.map q).sum-q (d+c-1)=A-Z-1+v2 ∧
      A-(P.first.map q).sum-q (d-1)-(P.second.map q).sum-q (d+c-1)-
        (P.third.map q).sum-q (d+c+b-1)=A-(T*Z+T+1)+v3+(Z+1)*w-(T*Z+T+1)*xt := by
    refine ⟨hc0.1,hc0.2.1,?_⟩
    change A-(P0.first.map q).sum-q (d-1)-(P0.second.map q).sum-q (d+c-1)-
      ((P0.third++X xt).map q).sum-q (d+c+b-1)=_
    rw [List.map_append,List.sum_append,hxq]
    linarith only [hc0.2.2]
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
  · exact ⟨hs.1,by rw [hcharges.1]; exact hs.2.1⟩
  · exact ⟨hs.2.2.1,by rw [hcharges.2.1]; exact hs.2.2.2.1⟩
  · exact ⟨hs.2.2.2.2.1,by rw [hcharges.2.2]; exact hs.2.2.2.2.2⟩
  · exact tot.1
  · exact tot.2


open private descending_edge_polynomials
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Descending

set_option maxHeartbeats 1400000 in
private theorem descending_edge_actual (b : ℕ) (hb : 2≤b) :
    (baseWord (b+1) b 2).Perm (List.range ((b+1)+b+2+(b+3))) ∧
      Strong (old (b+1) b 2 (b+3)) (charge (b+1) b 2 (b+3))
        (2^(b+3-1)*2^(b+1)*2^b*2^2) 0 (seedZ (b+1) b 2) (baseWord (b+1) b 2) := by
  let T : ℕ:=2^b
  let u1:=T ||| 4 ||| 1
  let A:=seedZ (b+1) b 2
  let e1:=8*(T:ℤ)^3+8*(T:ℤ)^2+4*T
  let e2:=32*(T:ℤ)^2+16*T
  let e3:=16*(T:ℤ)^2
  have hT : (T:ℤ)=4 ∨ 8≤(T:ℤ) := by
    by_cases he : b=2
    · left; norm_num [T,he]
    · right; exact_mod_cast (Nat.pow_le_pow_right Nat.zero_lt_two (show 3≤b by omega))
  have hu1 : (u1:ℤ)=if (T:ℤ)=4 then (5:ℤ) else (T:ℤ)+5 := by
    by_cases he : b=2
    · norm_num [T,u1,he]
    · have h8 : 8≤T:=Nat.pow_le_pow_right Nat.zero_lt_two (show 3≤b by omega)
      have h8i : (8:ℤ)≤T := by exact_mod_cast h8
      have hor : (5:ℕ) ||| T=5+T:=Nat.or_two_pow_eq_add_of_lt (show 5<T by omega)
      have h5 : (4 ||| 1:ℕ)=5 := by decide
      dsimp only [u1]
      rw [Nat.or_assoc,h5,Nat.or_comm,hor]
      simp only [Nat.cast_add,Nat.cast_ofNat,if_neg (show ¬(T:ℤ)=4 by omega)]
      ring
  have h5sub : ∀ e, (5:ℕ).testBit e=true → u1.testBit e=true := by
    intro e he
    have h5 : (5:ℕ)=4 ||| 1 := by decide
    rw [h5,Nat.testBit_or,Bool.or_eq_true] at he
    dsimp [u1]
    simp only [Nat.testBit_or,Bool.or_eq_true]
    rcases he with he|he
    · exact Or.inl (Or.inr he)
    · exact Or.inr he
  have hcap : u1<2^(b+2) := by
    apply Nat.or_lt_two_pow
    · apply Nat.or_lt_two_pow
      · exact Nat.pow_lt_pow_right (show 1<(2:ℕ) by decide) (by omega)
      · exact Nat.pow_lt_pow_right (show 1<(2:ℕ) by decide) (show 2<b+2 by omega)
    · have hp : 2≤(2:ℕ)^(b+2):=Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤b+2 by omega)
      omega
  have h5cap : 5<2^(b+2) := by
    have hp : 8≤(2:ℕ)^(b+2):=Nat.pow_le_pow_right Nat.zero_lt_two (show 3≤b+2 by omega)
    omega
  have hxcap : 1<2^(b+1-1) := by
    have hp : 2≤(2:ℕ)^(b+1-1):=Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤b+1-1 by omega)
    omega
  have hword : baseWord (b+1) b 2=advancedWord (b+1) b 2 (b+3) u1 5 5 0 0 0 0 1 := by
    have hmono : min (b+1) 2≤b ∧ b≤max (b+1) 2 := by
      rw [min_eq_right (by omega),max_eq_left (by omega)]; omega
    have hd : max (max (b+1) b) 2+2=b+3 := by
      rw [max_eq_left (by omega),max_eq_left (by omega)]
    have he : (2:ℕ)^(b+1)=2*2^b := by rw [pow_succ]; ring
    have hz (len off : ℕ) : labels len off 0=[] := by simp [labels]
    dsimp only [baseWord,baseBlocks]
    rw [if_pos hmono]
    simp only [monotoneBlocks,if_pos (show 2≤b ∧ b≤b+1 by omega),hd,
      show (2:ℕ)^2=4 by norm_num,he,if_pos (And.intro rfl rfl),
      advancedWord,advancedBlocks,maskedBlocks,Blocks.word,Nat.xor_self,Nat.xor_zero,
      Nat.zero_or,hz,List.append_nil,List.nil_append]
    rfl
  have hinv : (advancedWord (b+1) b 2 (b+3) u1 5 5 0 0 0 0 1).Perm
      (List.range ((b+1)+b+2+(b+3))) := by
    apply (advanced_permutation _ _ _ _ _ _ _ _ _ _ _ _).trans
    apply masked_inventory _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
    · intro e _ he; exact h5sub e he
    · intro e _ he; exact he
    · intro e _ he; simp at he
    · simp
    · simp
    · simp
  rw [hword]
  refine ⟨hinv,?_⟩
  apply actual_advanced_strong_exact (b+1) b 2 (b+3) u1 5 5 0 0 0 0 1
      (by omega) hb (by omega) (by omega)
  · simpa only [show b+3-1=b+2 by omega] using hcap
  · simpa only [show b+3-1=b+2 by omega] using h5cap
  · simpa only [show b+3-1=b+2 by omega] using h5cap
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _
  · exact hxcap
  · intro e _ he; exact h5sub e he
  · intro e _ he; exact he
  · simp
  · simp
  · have hp:=descending_edge_polynomials (T:ℤ) hT
    dsimp only at hp
    rw [←hu1] at hp
    have hA : A=10*(T:ℤ)^2+2*T+1 := by
      dsimp [A,seedZ,T]; rw [pow_succ]; norm_num; ring
    rw [←hA] at hp
    change e1≤A*u1 ∧ A*u1≤2*e1-A+1 ∧ e2≤5*A ∧ 5*A≤2*e2-A+5 ∧
      e3≤5*A-2*e3 ∧ 5*A-2*e3≤2*e3-A+2*(5*(T:ℤ)+1) at hp
    dsimp only
    have hH : (2:ℤ)^(b+3-1)=4*(T:ℤ) := by
      rw [show b+3-1=b+2 by omega,pow_add]; dsimp [T]; push_cast; norm_num; ring
    have hR : (2:ℤ)^(b+1)=2*(T:ℤ) := by rw [pow_succ]; dsimp [T]; push_cast; ring
    rw [hH,hR]
    norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,pow_succ] at *
    dsimp only [e1,e2,e3,A,T] at hp ⊢
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hp ⊢
    ring_nf at hp ⊢
    exact hp

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
