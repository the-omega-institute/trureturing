/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/Banks
   generality: I
   mirror-B: none(waiver:private-consumed-physical-banks)
   mirror-E: none(waiver:private-consumed-physical-banks)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Low and shifted high V inventories, one physical W singleton, and four banks. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks

/-! Physical paid-V construction. A shifted decoder keeps the high V block literal:
bit e of h is the physical V[c-d+e], never a divisible surrogate mass.
Its mask in the original V coordinates is 2^(c-d)*h. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source (size negatives chainLength chainStart)

private def full (a b c d : ℕ) (r : Fin 4) : ℕ := 2^(chainLength a b c d r-1)-1
private def stock (a b c d : ℕ) (r : Fin 4) (mask : ℕ) : List ℕ :=
  chamberLabels (chainLength a b c d r-1) (chainStart b c d r) mask
private def complement (a b c d : ℕ) (r : Fin 4) (mask : ℕ) : List ℕ :=
  stock a b c d r (full a b c d r ^^^ mask)
private def lowV (c d : ℕ) : List ℕ := chamberLabels (c-d) d (2^(c-d)-1)
private def highV (c d mask : ℕ) : List ℕ := chamberLabels (d-1) (d+(c-d)) mask
private def highComplement (c d h : ℕ) : List ℕ := highV c d ((2^(d-1)-1) ^^^ h)
private def terminals (a b c d : ℕ) : Fin 4→ℕ :=
  ![d-1,d+c-1,d+c+b-1,a+b+c+d-1]
private def banks (a b c d h : ℕ) : Fin 4→List ℕ :=
  ![stock a b c d 0 (full a b c d 0)++lowV c d,
    highComplement c d h,
    complement a b c d 2 (2^(b-a-1))++highV c d h,
    stock a b c d 3 (full a b c d 3)++stock a b c d 2 (2^(b-a-1))]
private def word (a b c d h : ℕ) : List ℕ :=
  let P:=banks a b c d h
  let T:=terminals a b c d
  P 0++[T 0]++P 1++[T 1]++P 2++[T 2]++P 3++[T 3]

private theorem stock_split (a b c d : ℕ) (r : Fin 4) (mask : ℕ) :
    (complement a b c d r mask++stock a b c d r mask).Perm
      (stock a b c d r (full a b c d r)) := by
  apply chamberLabels_split
  intro e he _
  simp [full,Nat.testBit_two_pow_sub_one,he]

private theorem high_split (c d h : ℕ) :
    (highComplement c d h++highV c d h).Perm (highV c d (2^(d-1)-1)) := by
  apply chamberLabels_split
  intro e he _
  simp [Nat.testBit_two_pow_sub_one,he]

/-- The two V blocks exhaust the original V interval, with no overlaps. -/
private theorem v_inventory (a b c d : ℕ) (hcd : d≤c) (hd : 1≤d) :
    lowV c d++highV c d (2^(d-1)-1)=stock a b c d 1 (full a b c d 1) := by
  simp only [lowV,highV,stock,full,chainLength,chainStart,
    Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Matrix.cons_val_zero',Matrix.cons_val_succ',chamberLabels_full]
  have he : c-d+(d-1)=c-1 := by omega
  simpa only [he] using (List.range'_append_1 (s:=d) (m:=c-d) (n:=d-1))

private theorem canonical_inventory (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    (stock a b c d 0 (full a b c d 0)++[d-1]++
      stock a b c d 1 (full a b c d 1)++[d+c-1]++
      stock a b c d 2 (full a b c d 2)++[d+c+b-1]++
      stock a b c d 3 (full a b c d 3)++[a+b+c+d-1])=List.range (a+b+c+d) := by
  simp only [stock,full,chamberLabels_full,chainLength,chainStart,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Matrix.cons_val_zero',Matrix.cons_val_succ']
  have merge (off len : ℕ) (hl : 1≤len) :
      List.range' off (len-1)++[off+len-1]=List.range' off len := by
    simpa only [show off+(len-1)=off+len-1 by omega,show len-1+1=len by omega]
      using (List.range'_1_concat (s:=off) (n:=len-1)).symm
  have h0:=merge 0 d (by omega)
  have h1:=merge d c (by omega)
  have h2:=merge (d+c) b (by omega)
  have h3:=merge (d+c+b) a (by omega)
  simp only [Nat.zero_add] at h0
  have h3' : List.range' (d+c+b) (a-1)++[a+b+c+d-1]=List.range' (d+c+b) a := by
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h3
  have join (m n : ℕ) : List.range' 0 m++List.range' m n=List.range' 0 (m+n) := by
    simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=m) (n:=n))
  calc
    _ = (List.range' 0 (d-1)++[d-1])++(List.range' d (c-1)++[d+c-1])++
        (List.range' (d+c) (b-1)++[d+c+b-1])++
        (List.range' (d+c+b) (a-1)++[a+b+c+d-1]) := by simp only [List.append_assoc]
    _ = List.range' 0 d++List.range' d c++List.range' (d+c) b++List.range' (d+c+b) a := by
      rw [h0,h1,h2,h3']
    _ = List.range (a+b+c+d) := by
      rw [join,join,join,←List.range_eq_range']
      congr 1
      omega

private theorem banks_inventory (a b c d h : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (hcd : d≤c) :
    (word a b c d h).Perm (List.range (a+b+c+d)) := by
  have hs:=Multiset.coe_eq_coe.mpr (high_split c d h)
  have hw:=Multiset.coe_eq_coe.mpr (stock_split a b c d 2 (2^(b-a-1)))
  have hv:=congrArg (fun l : List ℕ => (l : Multiset ℕ)) (v_inventory a b c d hcd (by omega))
  simp only [←Multiset.coe_add] at hs hw hv
  apply Multiset.coe_eq_coe.mp
  rw [←canonical_inventory a b c d ha hb hc hd]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  rw [←hv,←hs,←hw]
  dsimp [word,banks,terminals]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  ac_rfl

private theorem stock_good (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (r : Fin 4) (mask i : ℕ) (hi : i∈stock a b c d r mask) :
    i<size a b c d ∧ i∉negatives a b c d := by
  obtain ⟨e,he,_,rfl⟩:=(chamberLabels_mem _ _ _ _).mp hi
  fin_cases r <;> simp [chainLength,chainStart] at he ⊢
  all_goals simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
  all_goals omega

private theorem banks_good (a b c d h : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (hcd : d≤c)
    (r : Fin 4) (i : ℕ) (hi : i∈banks a b c d h r) :
    i<size a b c d ∧ i∉negatives a b c d := by
  have lo (i : ℕ) (hi : i∈lowV c d) : i<size a b c d ∧ i∉negatives a b c d := by
    obtain ⟨e,he,_,rfl⟩:=(chamberLabels_mem _ _ _ _).mp hi
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    omega
  have high (mask i : ℕ) (hi : i∈highV c d mask) : i<size a b c d ∧ i∉negatives a b c d := by
    obtain ⟨e,he,_,rfl⟩:=(chamberLabels_mem _ _ _ _).mp hi
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    omega
  fin_cases r <;> dsimp [banks,complement,highComplement] at hi
  all_goals try (simp only [List.mem_append] at hi;rcases hi with hi|hi)
  all_goals first | exact lo i hi | exact high _ i hi
                  | exact stock_good a b c d ha hb hc hd _ _ i hi

private theorem stock_mass (a b c d : ℕ) (r : Fin 4) (mask : ℕ)
    (hm : mask<2^(chainLength a b c d r-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    ((stock a b c d r mask).map f).sum=(mask:ℤ)*F r := by
  exact chamberLabels_sum _ _ _ hm f (F r) (hf r)

private theorem complement_mass (a b c d : ℕ) (r : Fin 4) (mask : ℕ)
    (hm : mask<2^(chainLength a b c d r-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    ((complement a b c d r mask).map f).sum=((full a b c d r:ℕ)-(mask:ℤ))*F r := by
  have hfull : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full];have := Nat.two_pow_pos (chainLength a b c d r-1);omega
  have hs:=((stock_split a b c d r mask).map f).sum_eq
  simp only [List.map_append,List.sum_append] at hs
  rw [stock_mass a b c d r mask hm f F hf,stock_mass a b c d r _ hfull f F hf] at hs
  linarith only [hs]

private theorem high_mass (a b c d mask : ℕ) (hcd : d≤c) (hd : 1≤d)
    (hm : mask<2^(d-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    ((highV c d mask).map f).sum=(2^(c-d):ℤ)*(mask:ℤ)*F 1 := by
  have hh : ∀ e<d-1, f (d+(c-d)+e)=2^e*((2:ℤ)^(c-d)*F 1) := by
    intro e he
    have hfe:=hf 1 (c-d+e) (by simp [chainLength];omega)
    simpa [chainStart,pow_add,mul_assoc,mul_left_comm,mul_comm,Nat.add_assoc] using hfe
  have hh':=chamberLabels_sum (d-1) (d+(c-d)) mask hm f ((2:ℤ)^(c-d)*F 1) hh
  simpa [highV,mul_assoc,mul_comm,mul_left_comm] using hh'

/-- The high stock is literally the d-1 available bits above the low block.
The stock weight is m*(t/2-1), not merely some divisible available mass. -/
private theorem v_stock_masks (c d : ℕ) (hcd : d≤c) (hd : 1≤d) :
    2^(c-1)-1=(2^(c-d)-1)+2^(c-d)*(2^(d-1)-1) := by
  have he : c-1=(c-d)+(d-1) := by omega
  rw [he,pow_add]
  have hp : 0<2^(c-d) := by positivity
  have hq : 0<2^(d-1) := by positivity
  have hpq:=Nat.mul_le_mul_left (2^(c-d)) (show 1≤2^(d-1) by omega)
  simp only [Nat.mul_one] at hpq
  rw [Nat.mul_sub_left_distrib]
  simp only [Nat.mul_one]
  omega

private theorem banks_masses (a b c d h : ℕ)
    (ha : 2≤a) (hab : a<b) (hcd : d≤c) (hd : 2≤d) (hh : h<2^(d-1))
    (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    let C:=fun r : Fin 4 => (full a b c d r:ℤ)
    let m : ℤ:=2^(c-d)
    let w : ℤ:=2^(b-a-1)
    (fun r => (((banks a b c d h) r).map f).sum)=
      ![C 0*F 0+(m-1)*F 1,m*(C 0-h)*F 1,
        (C 2-w)*F 2+m*h*F 1,C 3*F 3+w*F 2] := by
  dsimp only
  have hfull (r : Fin 4) : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full];have := Nat.two_pow_pos (chainLength a b c d r-1);omega
  have hw : 2^(b-a-1)<2^(chainLength a b c d 2-1) := by
    dsimp [chainLength]
    exact (Nat.pow_lt_pow_right (by omega : 1<2) (by omega))
  have mU:=stock_mass a b c d 0 _ (hfull 0) f F hf
  have mX:=stock_mass a b c d 3 _ (hfull 3) f F hf
  have mW:=stock_mass a b c d 2 _ hw f F hf
  have nW:=complement_mass a b c d 2 _ hw f F hf
  have hlo : ((lowV c d).map f).sum=((2:ℤ)^(c-d)-1)*F 1 := by
    have hm : 2^(c-d)-1<2^(c-d) := by have := Nat.two_pow_pos (c-d);omega
    have hh':=chamberLabels_sum (c-d) d (2^(c-d)-1) hm f (F 1)
      (fun e he => by simpa [chainStart] using hf 1 e (by simp [chainLength];omega))
    simpa [lowV,Nat.cast_sub (show 1≤2^(c-d) by have := Nat.two_pow_pos (c-d);omega)] using hh'
  have mH:=high_mass a b c d h hcd (by omega) hh f F hf
  have hHF : ((highV c d (2^(d-1)-1)).map f).sum=
      (2^(c-d):ℤ)*(full a b c d 0:ℤ)*F 1 := by
    simpa [full,chainLength] using high_mass a b c d (2^(d-1)-1) hcd (by omega)
      (by have := Nat.two_pow_pos (d-1);omega) f F hf
  have nH : ((highComplement c d h).map f).sum=
      (2^(c-d):ℤ)*((full a b c d 0:ℤ)-h)*F 1 := by
    have hs:=((high_split c d h).map f).sum_eq
    simp only [List.map_append,List.sum_append,mH,hHF] at hs
    nlinarith only [hs]
  funext r
  fin_cases r <;> dsimp [banks]
  all_goals simp only [List.map_append,List.sum_append,mU,mX,mW,nW,hlo,mH,nH,
    Nat.cast_pow,Nat.cast_ofNat]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV
