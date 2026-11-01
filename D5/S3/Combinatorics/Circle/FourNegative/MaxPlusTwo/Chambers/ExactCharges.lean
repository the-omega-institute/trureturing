/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/ExactCharges
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/ExactCharges
   mirror-E: none(waiver:internal-charge-bridge)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact remaining charges at the actual four-block physical seams. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks

/-! Exact source charge is retained when the reserve bound cannot be made conservative. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private seedZ charge from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private source_shadow_charge two_power_pred
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source
open private masked_weighted_masses
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks

set_option maxHeartbeats 1000000 in
-- The physical decoder sums charge with bases zero, one, Z+1 and TZ+T+1.
private theorem masked_remaining_charges
    (a b c d u1 u2 u3 v0 v2 v3 w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 3≤d)
    (hu1 : u1<2^(d-1)) (hu2 : u2<2^(d-1)) (hu3 : u3<2^(d-1))
    (hv0 : v0<2^(c-1)) (hv2 : v2<2^(c-1)) (hv3 : v3<2^(c-1))
    (hw : w<2^(b-1))
    (hU12 : ∀ e<d-1, u2.testBit e=true → u1.testBit e=true)
    (hU23 : ∀ e<d-1, u3.testBit e=true → u2.testBit e=true)
    (hV23 : ∀ e<c-1, v3.testBit e=true → v2.testBit e=true)
    (hVxor : (v0 ||| v2) ^^^ v2=v0) :
    let A:=seedZ a b c; let Z:ℤ:=2^c; let T:ℤ:=2^b
    let q:=charge a b c d
    let P:=maskedBlocks a b c d u1 u2 u3 v0 v2 v3 w
    A-(P.first.map q).sum-q (d-1)=A-1-v0 ∧
    A-(P.first.map q).sum-q (d-1)-(P.second.map q).sum-q (d+c-1)=A-Z-1+v2 ∧
    A-(P.first.map q).sum-q (d-1)-(P.second.map q).sum-q (d+c-1)-
      (P.third.map q).sum-q (d+c+b-1)=A-(T*Z+T+1)+v3+(Z+1)*w := by
  let A:=seedZ a b c
  let Z:ℤ:=2^c
  let T:ℤ:=2^b
  let q:=charge a b c d
  let P:=maskedBlocks a b c d u1 u2 u3 v0 v2 v3 w
  obtain ⟨u,v,ww,x,_⟩:=source_shadow_charge a b c d ha hb hc hd
  change (∀ i<d, q i=(if i+1<d then 0 else 1) ∧ _) at u
  change (∀ i<c, q (d+i)=(if i+1<c then 2^i else 2^(c-1)+1) ∧ _) at v
  change (∀ i<b, q (d+c+i)=(if i+1<b then 2^i*(Z+1) else 2^(b-1)*(Z+1)+1) ∧ _) at ww
  change (∀ i<a, q (d+c+b+i)=(if i+1<a then 2^i*(T*Z+T+1) else 2^(a-1)*(T*Z+T+1)+1) ∧ _) at x
  have hqU (e : ℕ) (he : e<d-1) : q (0+e)=2^e*0 := by
    simpa only [Nat.zero_add,if_pos (show e+1<d by omega),mul_zero] using (u e (by omega)).1
  have hqV (e : ℕ) (he : e<c-1) : q (d+e)=2^e*1 := by
    simpa only [if_pos (show e+1<c by omega),mul_one] using (v e (by omega)).1
  have hqW (e : ℕ) (he : e<b-1) : q (d+c+e)=2^e*(Z+1) := by
    simpa only [if_pos (show e+1<b by omega)] using (ww e (by omega)).1
  have hqX (e : ℕ) (he : e<a-1) : q (d+c+b+e)=2^e*(T*Z+T+1) := by
    simpa only [if_pos (show e+1<a by omega)] using (x e (by omega)).1
  have cap (n : ℕ) : 2^n-1<2^n:=Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have castfull (n : ℕ) : ((2^n-1:ℕ):ℤ)=(2:ℤ)^n-1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have fullU:=chamberLabels_sum (d-1) 0 (2^(d-1)-1) (cap _) q 0 hqU
  have fullV:=chamberLabels_sum (c-1) d (2^(c-1)-1) (cap _) q 1 hqV
  have fullW:=chamberLabels_sum (b-1) (d+c) (2^(b-1)-1) (cap _) q (Z+1) hqW
  have fullX:=chamberLabels_sum (a-1) (d+c+b) (2^(a-1)-1) (cap _) q (T*Z+T+1) hqX
  simp only [castfull,mul_zero,mul_one] at fullU fullV fullW fullX
  have hm:=masked_weighted_masses a b c d u1 u2 u3 v0 v2 v3 w q
    0 1 (Z+1) 0 (2^(c-1)-1) ((2^(b-1)-1)*(Z+1)) ((2^(a-1)-1)*(T*Z+T+1))
    hu1 hu2 hu3 hv0 hv2 hv3 hw hU12 hU23 hV23 hVxor hqU hqV hqW fullU fullV fullW fullX
  change (P.first.map q).sum=_ ∧ (P.second.map q).sum=_ ∧
    (P.third.map q).sum=_ ∧ (P.fourth.map q).sum=_ at hm
  simp only [mul_zero,zero_mul,one_mul,zero_add,sub_zero] at hm
  have hn1:=(u (d-1) (by omega)).1
  have hn2:=(v (c-1) (by omega)).1
  have hn3:=(ww (b-1) (by omega)).1
  simp only [if_neg (show ¬d-1+1<d by omega)] at hn1
  simp only [if_neg (show ¬c-1+1<c by omega)] at hn2
  simp only [if_neg (show ¬b-1+1<b by omega)] at hn3
  rw [show d+(c-1)=d+c-1 by omega] at hn2
  rw [show d+c+(b-1)=d+c+b-1 by omega] at hn3
  have hZ : Z=2*(2:ℤ)^(c-1):=two_power_pred c (by omega)
  have hT : T=2*(2:ℤ)^(b-1):=two_power_pred b (by omega)
  change A-(P.first.map q).sum-q (d-1)=A-1-v0 ∧
    A-(P.first.map q).sum-q (d-1)-(P.second.map q).sum-q (d+c-1)=A-Z-1+v2 ∧
    A-(P.first.map q).sum-q (d-1)-(P.second.map q).sum-q (d+c-1)-
      (P.third.map q).sum-q (d+c+b-1)=A-(T*Z+T+1)+v3+(Z+1)*w
  rw [hm.1,hm.2.1,hm.2.2.1,hn1,hn2,hn3,hZ,hT]
  constructor
  · ring
  constructor <;> ring


private theorem remaining_charge_bounds (A : ℤ) (b c v0 v2 v3 w : ℕ)
    (hv2 : v2<2^(c-1)) (hv3 : v3<2^(c-1)) (hw : w<2^(b-1)) :
    let Z:ℤ:=2^c; let T:ℤ:=2^b
    A-1-v0≤A ∧ A-Z-1+v2≤A ∧ A-(T*Z+T+1)+v3+(Z+1)*w≤A := by
  let Z:ℤ:=2^c
  let T:ℤ:=2^b
  have hvcap : (2:ℕ)^(c-1)≤2^c :=
    Nat.pow_le_pow_right Nat.zero_lt_two (Nat.sub_le c 1)
  have hwcap : (2:ℕ)^(b-1)≤2^b :=
    Nat.pow_le_pow_right Nat.zero_lt_two (Nat.sub_le b 1)
  have hv2i : (v2:ℤ)<Z := by dsimp [Z]; exact_mod_cast lt_of_lt_of_le hv2 hvcap
  have hv3i : (v3:ℤ)≤Z := by dsimp [Z]; exact_mod_cast le_of_lt (lt_of_lt_of_le hv3 hvcap)
  have hwi : (w:ℤ)≤T-1 := by
    have hh : (w:ℤ)<T := by dsimp [T]; exact_mod_cast lt_of_lt_of_le hw hwcap
    omega
  have hmult:=mul_le_mul_of_nonneg_left hwi (show 0≤Z+1 by dsimp [Z]; positivity)
  change A-1-v0≤A ∧ A-Z-1+v2≤A ∧ A-(T*Z+T+1)+v3+(Z+1)*w≤A
  exact ⟨by omega,by omega,by nlinarith only [hmult,hv3i]⟩

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
