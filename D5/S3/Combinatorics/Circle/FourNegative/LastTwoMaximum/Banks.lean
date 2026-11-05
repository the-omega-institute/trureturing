/- GID: D5/S3/Combinatorics/Circle/FourNegative/LastTwoMaximum/Banks
   generality: I
   mirror-B: none(waiver:private-consumed-physical-inventory)
   mirror-E: none(waiver:private-consumed-physical-inventory)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Literal hybrid inventories and their exact old and new scalar masses. -/
import D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Source
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
namespace StrictDictionary
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private vNat mask
  from D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Source
open private stock full stock_split canonical_inventory stock_good stock_mass complement_mass
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source (size negatives chainLength chainStart)

/- The high decoder uses the original V index b-2+e.  A mask weight is
   never used as a physical label.  In particular the W tail is decoded
   by `stock ... 2 w`, rather than the incorrect singleton [2*s+w]. -/
private def hybridLabels (b s t : ℕ) : List ℕ :=
  chamberLabels (b-2) 0 (t % vNat b) ++
    chamberLabels (s-b+1) (s+(b-2)) (t / vNat b)

private def firstBank (b s : ℕ) : List ℕ :=
  chamberLabels (b-2) s (2^(b-2)-1) ++
    chamberLabels (s-b+1) (b-2) (2^(s-b+1)-1)

private def borrowBanks (a b s t u : ℕ) : Fin 4 → List ℕ :=
  ![firstBank b s,
    hybridLabels b s (mask s ^^^ t),
    stock a b s s 2 (full a b s s 2) ++ hybridLabels b s (t ^^^ u),
    stock a b s s 3 (full a b s s 3) ++ hybridLabels b s u]

private def singletonBanks (a b s t w : ℕ) : Fin 4 → List ℕ :=
  ![firstBank b s,
    hybridLabels b s (mask s ^^^ t),
    stock a b s s 2 (full a b s s 2 ^^^ w) ++ hybridLabels b s t,
    stock a b s s 3 (full a b s s 3) ++ stock a b s s 2 w]

private def terminals (a b s : ℕ) : Fin 4 → ℕ :=
  ![s-1, s+s-1, s+s+b-1, a+b+s+s-1]

private def banksWord (a b s : ℕ) (P : Fin 4 → List ℕ) : List ℕ :=
  P 0 ++ [terminals a b s 0] ++ P 1 ++ [terminals a b s 1] ++
    P 2 ++ [terminals a b s 2] ++ P 3 ++ [terminals a b s 3]

private theorem hybrid_split (b s outer inner : ℕ)
    (hsub : ∀ e : ℕ, inner.testBit e = true → outer.testBit e = true) :
    (hybridLabels b s (outer ^^^ inner) ++ hybridLabels b s inner).Perm
      (hybridLabels b s outer) := by
  have hlo := chamberLabels_split (b-2) 0 (outer % vNat b) (inner % vNat b)
    (by
      intro e he hi
      simpa [vNat, Nat.testBit_mod_two_pow, he] using hsub e
        (by simpa [vNat, Nat.testBit_mod_two_pow, he] using hi))
  have hhi := chamberLabels_split (s-b+1) (s+(b-2))
    (outer / vNat b) (inner / vNat b)
    (by
      intro e _ hi
      simpa [vNat, Nat.testBit_div_two_pow] using hsub (e+(b-2))
        (by simpa [vNat, Nat.testBit_div_two_pow] using hi))
  apply Multiset.coe_eq_coe.mp
  have hl := Multiset.coe_eq_coe.mpr hlo
  have hh := Multiset.coe_eq_coe.mpr hhi
  dsimp [hybridLabels]
  simp only [vNat, Nat.xor_mod_two_pow, Nat.xor_div_two_pow] at *
  simp only [← Multiset.coe_add] at *
  calc
    _ = ((chamberLabels (b-2) 0 (outer % 2^(b-2) ^^^ inner % 2^(b-2)) :
          Multiset ℕ) + chamberLabels (b-2) 0 (inner % 2^(b-2))) +
        ((chamberLabels (s-b+1) (s+(b-2))
          (outer / 2^(b-2) ^^^ inner / 2^(b-2)) : Multiset ℕ) +
          chamberLabels (s-b+1) (s+(b-2)) (inner / 2^(b-2))) := by ac_rfl
    _ = _ := by rw [hl, hh]

private theorem hybrid_full_inventory (b s : ℕ) (hb : 2 ≤ b) (hbs : b ≤ s) :
    (firstBank b s ++ hybridLabels b s (mask s)).Perm
      (stock 2 b s s 0 (full 2 b s s 0) ++
        stock 2 b s s 1 (full 2 b s s 1)) := by
  let v := 2^(b-2)
  let q := 2^(s-b+1)
  have hv : 0 < v := by dsimp [v]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hp : 2^(s-1) = v*q := by
    dsimp [v,q]
    rw [← pow_add]
    congr 1
    omega
  have hm : mask s = (v-1) + v*(q-1) := by
    dsimp [mask]
    rw [hp, Nat.mul_sub_left_distrib]
    simp only [Nat.mul_one]
    have := Nat.mul_le_mul_left v (show 1 ≤ q by omega)
    simp only [Nat.mul_one] at this
    omega
  have hlo : mask s % vNat b = v-1 := by
    change mask s % v = v-1
    rw [hm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hhi : mask s / vNat b = q-1 := by
    change mask s / v = q-1
    rw [hm, Nat.add_mul_div_left _ _ hv, Nat.div_eq_of_lt (by omega)]
    omega
  have hU : chamberLabels (b-2) 0 (v-1) ++
      chamberLabels (s-b+1) (b-2) (q-1) = stock 2 b s s 0 (full 2 b s s 0) := by
    simp only [stock,full,chainLength,chainStart]
    dsimp [v,q]
    rw [chamberLabels_full,chamberLabels_full,chamberLabels_full]
    simpa only [Nat.zero_add, show b-2+(s-b+1)=s-1 by omega] using
      (List.range'_append_1 (s := 0) (m := b-2) (n := s-b+1))
  have hV : chamberLabels (b-2) s (v-1) ++
      chamberLabels (s-b+1) (s+(b-2)) (q-1) = stock 2 b s s 1 (full 2 b s s 1) := by
    simp only [stock,full,chainLength,chainStart]
    dsimp [v,q]
    rw [chamberLabels_full,chamberLabels_full,chamberLabels_full]
    simpa only [show b-2+(s-b+1)=s-1 by omega] using
      (List.range'_append_1 (s := s) (m := b-2) (n := s-b+1))
  apply Multiset.coe_eq_coe.mp
  rw [← hU, ← hV]
  dsimp [firstBank,hybridLabels]
  rw [hlo,hhi]
  change _ = _
  dsimp [v,q]
  simp only [← Multiset.coe_add]
  ac_rfl

private theorem hybrid_good (a b s t : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hbs : b ≤ s) (i : ℕ) (hi : i ∈ hybridLabels b s t) :
    i < size a b s s ∧ i ∉ negatives a b s s := by
  simp only [hybridLabels,List.mem_append] at hi
  rcases hi with hi | hi
  all_goals obtain ⟨e,he,_,rfl⟩ := (chamberLabels_mem _ _ _ _).mp hi
  all_goals simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
  all_goals omega

private theorem first_good (a b s : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hbs : b ≤ s) (i : ℕ) (hi : i ∈ firstBank b s) :
    i < size a b s s ∧ i ∉ negatives a b s s := by
  simp only [firstBank,List.mem_append] at hi
  rcases hi with hi | hi
  all_goals obtain ⟨e,he,_,rfl⟩ := (chamberLabels_mem _ _ _ _).mp hi
  all_goals simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
  all_goals omega

private theorem borrow_inventory (a b s t u : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hbs : b ≤ s)
    (hsub : ∀ e : ℕ, u.testBit e = true → t.testBit e = true) :
    (banksWord a b s (borrowBanks a b s t u)).Perm (List.range (a+b+s+s)) := by
  /- A truncated decoder needs containment only at its available bit indices. -/
  have hsplit : (hybridLabels b s (mask s ^^^ t) ++ hybridLabels b s t).Perm
      (hybridLabels b s (mask s)) := by
    /- Use the canonical split at each decoder, so bits above s-2 disappear. -/
    have lo := chamberLabels_split (b-2) 0
      (mask s % vNat b) (t % vNat b)
      (by intro e he _; simp [vNat,Nat.testBit_mod_two_pow,he,mask,
        Nat.testBit_two_pow_sub_one,show e < s-1 by omega])
    have hi := chamberLabels_split (s-b+1) (s+(b-2))
      (mask s / vNat b) (t / vNat b)
      (by intro e he _; simp [vNat,Nat.testBit_div_two_pow,mask,
        Nat.testBit_two_pow_sub_one,show e+(b-2)<s-1 by omega])
    apply Multiset.coe_eq_coe.mp
    have hl := Multiset.coe_eq_coe.mpr lo
    have hh := Multiset.coe_eq_coe.mpr hi
    simp only [← Multiset.coe_add] at hl hh
    dsimp [hybridLabels]
    simp only [vNat,Nat.xor_mod_two_pow,Nat.xor_div_two_pow,←Multiset.coe_add] at *
    calc
      _ = ((chamberLabels (b-2) 0 (mask s % 2^(b-2) ^^^ t % 2^(b-2)) :
          Multiset ℕ) + chamberLabels (b-2) 0 (t % 2^(b-2))) +
        ((chamberLabels (s-b+1) (s+(b-2))
          (mask s / 2^(b-2) ^^^ t / 2^(b-2)) : Multiset ℕ) +
          chamberLabels (s-b+1) (s+(b-2)) (t / 2^(b-2))) := by ac_rfl
      _ = _ := by rw [hl, hh]
  have htu := Multiset.coe_eq_coe.mpr (hybrid_split b s t u hsub)
  have hmt := Multiset.coe_eq_coe.mpr hsplit
  have hstock := Multiset.coe_eq_coe.mpr (hybrid_full_inventory b s hb hbs)
  simp only [←Multiset.coe_add] at htu hmt hstock
  have hstock' : (firstBank b s : Multiset ℕ) + hybridLabels b s (mask s) =
      (stock a b s s 0 (full a b s s 0) : Multiset ℕ) +
        stock a b s s 1 (full a b s s 1) := by
    simpa [stock,full,chainLength,chainStart] using hstock
  have hpaid : (firstBank b s : Multiset ℕ)+
      ((hybridLabels b s (mask s ^^^ t) : Multiset ℕ)+
        ((hybridLabels b s (t ^^^ u) : Multiset ℕ)+hybridLabels b s u))=
      (stock a b s s 0 (full a b s s 0) : Multiset ℕ)+
        stock a b s s 1 (full a b s s 1) := by
    rw [htu,hmt]
    exact hstock'
  have heq := congrArg (fun m : Multiset ℕ =>
    m+stock a b s s 2 (full a b s s 2)+stock a b s s 3 (full a b s s 3)+
      {s-1}+{s+s-1}+{s+s+b-1}+{a+b+s+s-1}) hpaid
  apply Multiset.coe_eq_coe.mp
  rw [←canonical_inventory a b s s ha hb (by omega) (by omega)]
  convert heq using 1 <;> dsimp [banksWord,borrowBanks,terminals]
  all_goals simp only [←Multiset.coe_add,Multiset.coe_singleton]
  all_goals ac_rfl

private theorem singleton_inventory (a b s t w : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hbs : b ≤ s) :
    (banksWord a b s (singletonBanks a b s t w)).Perm (List.range (a+b+s+s)) := by
  have hp := borrow_inventory a b s t 0 ha hb hbs (by simp)
  have hw := Multiset.coe_eq_coe.mpr (stock_split a b s s 2 w)
  simp only [←Multiset.coe_add] at hw
  change (stock a b s s 2 (full a b s s 2 ^^^ w) : Multiset ℕ)+
    stock a b s s 2 w=(stock a b s s 2 (full a b s s 2) : Multiset ℕ) at hw
  have hzero : hybridLabels b s 0 = [] := by simp [hybridLabels,vNat,chamberLabels,labels]
  have hp' := Multiset.coe_eq_coe.mpr hp
  have heq := congrArg (fun m : Multiset ℕ =>
    (firstBank b s : Multiset ℕ)+hybridLabels b s (mask s ^^^ t)+m+
      hybridLabels b s t+stock a b s s 3 (full a b s s 3)+
      {s-1}+{s+s-1}+{s+s+b-1}+{a+b+s+s-1}) hw
  have hsame : (banksWord a b s (singletonBanks a b s t w) : Multiset ℕ)=
      (banksWord a b s (borrowBanks a b s t 0) : Multiset ℕ) := by
    convert heq using 1 <;> dsimp [banksWord,singletonBanks,borrowBanks,terminals]
    all_goals simp only [Nat.xor_zero,hzero,List.append_nil,
      ←Multiset.coe_add,Multiset.coe_singleton]
    all_goals ac_rfl
  exact Multiset.coe_eq_coe.mp (hsame.trans hp')

private theorem hybrid_mass (b s t : ℕ) (hb : 2 ≤ b) (hbs : b ≤ s)
    (ht : t < 2^(s-1)) (f : ℕ → ℤ) (AA BB : ℤ)
    (hu : ∀ e < s-1, f e = 2^e*AA)
    (hv : ∀ e < s-1, f (s+e) = 2^e*BB) :
    ((hybridLabels b s t).map f).sum =
      ((t % vNat b : ℕ) : ℤ)*AA + ((t-t % vNat b : ℕ) : ℤ)*BB := by
  have hv0 : 0 < vNat b := by dsimp [vNat]; positivity
  have hp : 2^(s-1) = 2^(s-b+1)*vNat b := by
    dsimp [vNat]
    rw [←pow_add]
    congr 1
    omega
  have hhi : t/vNat b < 2^(s-b+1) := by
    apply (Nat.div_lt_iff_lt_mul hv0).mpr
    rwa [←hp]
  have lo := chamberLabels_sum (b-2) 0 (t % vNat b)
    (by exact Nat.mod_lt _ hv0) f AA (by intro e he; simpa using hu e (by omega))
  have hi := chamberLabels_sum (s-b+1) (s+(b-2)) (t/vNat b) hhi f
    ((vNat b : ℕ) * BB : ℤ) (by
      intro e he
      rw [show s+(b-2)+e=s+(b-2+e) by omega,hv _ (by omega),pow_add]
      dsimp [vNat]
      push_cast
      ring)
  have hdecomp : (t-t % vNat b : ℕ) = vNat b*(t/vNat b) := by
    have hh := Nat.mod_add_div t (vNat b)
    omega
  simp only [hybridLabels,List.map_append,List.sum_append,lo,hi,hdecomp,
    Nat.cast_mul]
  ring

private def mixedMass (b : ℕ) (F : Fin 4 → ℤ) (t : ℕ) : ℤ :=
  (t%vNat b : ℕ)*F 0+(t-t%vNat b : ℕ)*F 1

private theorem hybrid_complement_split (b s t : ℕ) (ht : t<2^(s-1)) :
    (hybridLabels b s (mask s ^^^ t)++hybridLabels b s t).Perm
      (hybridLabels b s (mask s)) := by
  apply hybrid_split
  intro e he
  by_cases hel : e<s-1
  · simp [mask,Nat.testBit_two_pow_sub_one,hel]
  · have hp : 2^(s-1) ≤ 2^e := Nat.pow_le_pow_right (by omega : 1≤2) (by omega)
    have hf := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ht hp)
    simp [hf] at he

private theorem first_mass (a b s : ℕ) (hb : 2≤b) (hbs : b≤s)
    (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b s s r-1,
      f (chainStart b s s r+e)=2^e*F r) :
    ((firstBank b s).map f).sum=(full a b s s 0 : ℤ)*F 0+
      ((vNat b : ℤ)-1)*(F 1-F 0) := by
  have vlo := chamberLabels_sum (b-2) s (2^(b-2)-1)
    (by have := Nat.two_pow_pos (b-2);omega) f (F 1)
    (by intro e he;simpa [chainStart] using hf 1 e (by simp [chainLength];omega))
  have uhi := chamberLabels_sum (s-b+1) (b-2) (2^(s-b+1)-1)
    (by have := Nat.two_pow_pos (s-b+1);omega) f ((vNat b : ℤ)*F 0)
    (by
      intro e he
      have hh := hf 0 (b-2+e) (by simp [chainLength];omega)
      simpa [chainStart,vNat,pow_add,mul_assoc,mul_left_comm,mul_comm] using hh)
  have hc : (full a b s s 0 : ℤ)=
      (vNat b : ℤ)*((2 : ℤ)^(s-b+1))-1 := by
    dsimp [full,chainLength,vNat]
    rw [Nat.cast_sub (by have := Nat.two_pow_pos (s-1);omega)]
    push_cast
    rw [←pow_add, show b-2+(s-b+1)=s-1 by omega]
  have castlo : ((2^(b-2)-1 : ℕ) : ℤ) = (2 : ℤ)^(b-2)-1 := by
    rw [Nat.cast_sub (show 1 ≤ 2^(b-2) by have := Nat.two_pow_pos (b-2); omega)]
    push_cast
    rfl
  have casthi : ((2^(s-b+1)-1 : ℕ) : ℤ) = (2 : ℤ)^(s-b+1)-1 := by
    rw [Nat.cast_sub (show 1 ≤ 2^(s-b+1) by have := Nat.two_pow_pos (s-b+1); omega)]
    push_cast
    rfl
  simp only [firstBank,List.map_append,List.sum_append,vlo,uhi]
  rw [hc,castlo,casthi]
  dsimp [vNat]
  push_cast
  ring

private theorem masks_masses (a b s t u : ℕ) (ha : 2≤a) (hb : 2≤b) (hbs : b≤s)
    (ht : t<2^(s-1)) (hu : u<2^(s-1))
    (hsub : ∀ e : ℕ, u.testBit e=true → t.testBit e=true)
    (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b s s r-1,
      f (chainStart b s s r+e)=2^e*F r) :
    let C := fun r : Fin 4 => (full a b s s r : ℤ)
    let E := C 0*F 0+((vNat b : ℤ)-1)*(F 1-F 0)
    (fun r : Fin 4 => ((borrowBanks a b s t u r).map f).sum)=
      ![E,C 0*F 0+C 1*F 1-E-mixedMass b F t,
        C 2*F 2+mixedMass b F t-mixedMass b F u,C 3*F 3+mixedMass b F u] := by
  dsimp only
  have fullbound (r : Fin 4) : full a b s s r<2^(chainLength a b s s r-1) := by
    dsimp [full];have := Nat.two_pow_pos (chainLength a b s s r-1);omega
  have stockmass (r : Fin 4) := stock_mass a b s s r _ (fullbound r) f F hf
  have hm (q : ℕ) (hq : q<2^(s-1)) :
      ((hybridLabels b s q).map f).sum=mixedMass b F q := by
    exact hybrid_mass b s q hb hbs hq f (F 0) (F 1)
      (fun e he => by simpa [chainStart] using hf 0 e (by simpa [chainLength]))
      (fun e he => by simpa [chainStart] using hf 1 e (by simpa [chainLength]))
  have ht' := hm t ht
  have hu' := hm u hu
  have hfirst := first_mass a b s hb hbs f F hf
  have hMmass : ((hybridLabels b s (mask s)).map f).sum=
      (full a b s s 0 : ℤ)*F 0+(full a b s s 1 : ℤ)*F 1-
        ((firstBank b s).map f).sum := by
    have hp := hybrid_full_inventory b s hb hbs
    have hp' : (firstBank b s++hybridLabels b s (mask s)).Perm
      (stock a b s s 0 (full a b s s 0)++stock a b s s 1 (full a b s s 1)) := by
      simpa [stock,full,chainLength,chainStart] using hp
    have hh := (hp'.map f).sum_eq
    simp only [List.map_append,List.sum_append,stockmass 0,stockmass 1] at hh
    omega
  have hcomp : ((hybridLabels b s (mask s ^^^ t)).map f).sum=
      (full a b s s 0 : ℤ)*F 0+(full a b s s 1 : ℤ)*F 1-
        ((firstBank b s).map f).sum-mixedMass b F t := by
    have hh := ((hybrid_complement_split b s t ht).map f).sum_eq
    simp only [List.map_append,List.sum_append,hMmass,ht'] at hh
    omega
  have hdiff : ((hybridLabels b s (t ^^^ u)).map f).sum=mixedMass b F t-mixedMass b F u := by
    have hh := ((hybrid_split b s t u hsub).map f).sum_eq
    simp only [List.map_append,List.sum_append,ht',hu'] at hh
    omega
  funext r
  fin_cases r <;> dsimp [borrowBanks]
  all_goals simp only [List.map_append,List.sum_append,hfirst,hcomp,hdiff,hu',stockmass]
  all_goals ring

private theorem singleton_masses (a b s t w : ℕ) (ha : 2≤a) (hb : 2≤b) (hbs : b≤s)
    (ht : t<2^(s-1)) (hw : w<2^(b-1))
    (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b s s r-1,
      f (chainStart b s s r+e)=2^e*F r) :
    let C := fun r : Fin 4 => (full a b s s r : ℤ)
    let E := C 0*F 0+((vNat b : ℤ)-1)*(F 1-F 0)
    (fun r : Fin 4 => ((singletonBanks a b s t w r).map f).sum)=
      ![E,C 0*F 0+C 1*F 1-E-mixedMass b F t,
        C 2*F 2+mixedMass b F t-(w : ℤ)*F 2,C 3*F 3+(w : ℤ)*F 2] := by
  have hbmass := masks_masses a b s t 0 ha hb hbs ht (by positivity) (by simp) f F hf
  have sm := stock_mass a b s s 2 w (by simpa [chainLength] using hw) f F hf
  have cm := complement_mass a b s s 2 w (by simpa [chainLength] using hw) f F hf
  have xm := stock_mass a b s s 3 (full a b s s 3)
    (by dsimp [full];have := Nat.two_pow_pos (chainLength a b s s 3-1);omega) f F hf
  funext r
  fin_cases r
  · exact congrFun hbmass 0
  · exact congrFun hbmass 1
  · have hm : ((hybridLabels b s t).map f).sum=mixedMass b F t := by
      exact hybrid_mass b s t hb hbs ht f (F 0) (F 1)
        (fun e he => by simpa [chainStart] using hf 0 e (by simpa [chainLength]))
        (fun e he => by simpa [chainStart] using hf 1 e (by simpa [chainLength]))
    change ((stock a b s s 2 (full a b s s 2 ^^^ w)).map f).sum = _ at cm
    dsimp [singletonBanks]
    rw [List.map_append,List.sum_append,cm,hm]
    ring
  · dsimp [singletonBanks]
    simp only [List.map_append,List.sum_append,xm,sm]

private theorem banks_good (a b s t u : ℕ) (ha : 2≤a) (hb : 2≤b) (hbs : b≤s)
    (P : Fin 4→List ℕ) (hP : P=borrowBanks a b s t u ∨ P=singletonBanks a b s t u)
    (r : Fin 4) (i : ℕ) (hi : i∈P r) :
    i<size a b s s ∧ i∉negatives a b s s := by
  rcases hP with rfl | rfl
  all_goals fin_cases r <;> dsimp [borrowBanks,singletonBanks] at hi
  all_goals try (simp only [List.mem_append] at hi;rcases hi with hi | hi)
  all_goals first
    | exact first_good a b s ha hb hbs i hi
    | exact hybrid_good a b s _ ha hb hbs i hi
    | exact stock_good a b s s ha hb (by omega) (by omega) _ _ i hi

end StrictDictionary
end D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
