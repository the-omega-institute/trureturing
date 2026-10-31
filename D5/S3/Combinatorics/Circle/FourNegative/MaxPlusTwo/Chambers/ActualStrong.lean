/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/ActualStrong
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/ActualStrong
   mirror-E: none(waiver:internal-source-bridge)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact and conservative reserve criteria for actual physical centered sources. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ExactCharges

/-! The actual physical source table realizes each of the four positive blocks. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open SourceWidth PeriodicShortening RunFirstEarTransport
open private mass_margin
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
open private source_shadow_charge
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source
open private seedZ modZ old enlarged charge shadow
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private Strong from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Strip
open private power_two_ge masked_inventory masked_weighted_masses actual_word_totals
  actual_chain_masses four_reserve_strong
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
open private masked_remaining_charges remaining_charge_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ExactCharges

set_option maxHeartbeats 1600000 in
/-- The reserve inequalities are realized by the actual physical centered sources. -/
private theorem actual_masked_strong_exact
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
      e1≤S1 ∧ S1≤2*e1-(A-1-v0) ∧ e2≤S2 ∧ S2≤2*e2-(A-Z-1+v2) ∧
        e3≤S3 ∧ S3≤2*e3-(A-(T*Z+T+1)+v3+(Z+1)*w)) :
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
  change e1≤S1 ∧ S1≤2*e1-(A-1-v0) ∧ e2≤S2 ∧ S2≤2*e2-(A-Z-1+v2) ∧
    e3≤S3 ∧ S3≤2*e3-(A-(T*Z+T+1)+v3+(Z+1)*w) at hs
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
  have hcharges:=masked_remaining_charges a b c d u1 u2 u3 v0 v2 v3 w
    ha hb hc hd hu1 hu2 hu3 hv0 hv2 hv3 hw hU12 hU23 hV23 hVxor
  change A-(P.first.map q).sum-q (d-1)=A-1-v0 ∧
    A-(P.first.map q).sum-q (d-1)-(P.second.map q).sum-q (d+c-1)=A-Z-1+v2 ∧
    A-(P.first.map q).sum-q (d-1)-(P.second.map q).sum-q (d+c-1)-
      (P.third.map q).sum-q (d+c+b-1)=A-(T*Z+T+1)+v3+(Z+1)*w at hcharges
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
  apply actual_masked_strong_exact a b c d u1 u2 u3 v0 v2 v3 w
    ha hb hc hd hu1 hu2 hu3 hv0 hv2 hv3 hw hU12 hU23 hV23 hVxor
  dsimp only at hs ⊢
  have hcharges:=remaining_charge_bounds (seedZ a b c) b c v0 v2 v3 w hv2 hv3 hw
  dsimp only at hcharges
  refine ⟨hs.1,?_,hs.2.2.1,?_,hs.2.2.2.2.1,?_⟩
  · linarith only [hs.2.1,hcharges.1]
  · linarith only [hs.2.2.2.1,hcharges.2.1]
  · linarith only [hs.2.2.2.2.2,hcharges.2.2]

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
