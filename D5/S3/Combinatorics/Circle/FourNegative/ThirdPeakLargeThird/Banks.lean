/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/Banks
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Three approved physical orders, sparse paid-bit partition, and actual bank masses. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Arithmetic

/-! ThirdPeakLargeThird: Banks. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private size negatives chainLength chainStart from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private full stock complement stock_split canonical_inventory stock_good stock_mass complement_mass terminals
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private blocksWord insertAt from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private withEar from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets

private def banks (a b c d v p : ℕ) (strict : Bool) : Fin 4→List ℕ :=
  ![stock a b c d 0 (full a b c d 0),
    (if strict then stock a b c d 3 (full a b c d 3)
      else stock a b c d 2 (full a b c d 2))++stock a b c d 1 p,
    (if strict then stock a b c d 2 (full a b c d 2)
      else stock a b c d 3 (full a b c d 3))++stock a b c d 1 (v ^^^ p),
    complement a b c d 1 v]
private def order (a b c d : ℕ) (strict : Bool) : Fin 4→ℕ :=
  ![if strict then terminals a b c d 2 else terminals a b c d 1,
    if strict then terminals a b c d 1 else terminals a b c d 2,
    terminals a b c d 3,terminals a b c d 0]
private def packets (a b c d v p : ℕ) (strict : Bool) : List (List ℕ×ℕ) :=
  let P:=banks a b c d v p strict
  let T:=order a b c d strict
  [(P 0,T 0),(P 1,T 1),(P 2,T 2),(P 3,T 3)]
private def word (a b c d v p : ℕ) (strict : Bool) : List ℕ :=
  blocksWord (packets a b c d v p strict)
private def earSlot (early : Bool) : ℕ := if early then 1 else 2
private def preEar (a b c d v p : ℕ) (strict early : Bool) : List ℕ :=
  let P:=banks a b c d v p strict
  let T:=order a b c d strict
  if early then P 0++[T 0]++P 1
  else P 0++[T 0]++P 1++[T 1]++P 2
private def postEar (a b c d v p : ℕ) (strict early : Bool) : List ℕ :=
  let P:=banks a b c d v p strict
  let T:=order a b c d strict
  if early then [T 1]++P 2++[T 2]++P 3++[T 3]
  else [T 2]++P 3++[T 3]
private def cut (a b c d v p : ℕ) (strict early : Bool) : ℕ :=
  (preEar a b c d v p strict early).length

private theorem v_split (a b c d v p : ℕ)
    (hsub : ∀ e<c-1,p.testBit e=true → v.testBit e=true) :
    (stock a b c d 1 (v ^^^ p)++stock a b c d 1 p).Perm (stock a b c d 1 v) := by
  simpa [stock,chainLength,chainStart] using chamberLabels_split (c-1) d v p hsub

private theorem inventory (a b c d v p : ℕ) (strict : Bool)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hsub : ∀ e<c-1,p.testBit e=true → v.testBit e=true) :
    (word a b c d v p strict).Perm (List.range (size a b c d)) := by
  have outer:=Multiset.coe_eq_coe.mpr (stock_split a b c d 1 v)
  have inner:=Multiset.coe_eq_coe.mpr (v_split a b c d v p hsub)
  simp only [←Multiset.coe_add] at outer inner
  apply Multiset.coe_eq_coe.mp
  change (word a b c d v p strict : Multiset ℕ)=(List.range (a+b+c+d) : Multiset ℕ)
  rw [←canonical_inventory a b c d ha hb hc hd]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  rw [←outer,←inner]
  cases strict <;> dsimp [word,packets,blocksWord,banks,order,terminals]
  all_goals simp only [←Multiset.coe_add,Multiset.coe_singleton]
  all_goals ac_rfl

private theorem banks_good (a b c d v p : ℕ) (strict : Bool)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (r : Fin 4) (i : ℕ) (hi : i∈banks a b c d v p strict r) :
    i<size a b c d ∧ i∉negatives a b c d := by
  cases strict <;> fin_cases r <;> dsimp [banks,complement] at hi
  all_goals try (simp only [List.mem_append] at hi;rcases hi with hi|hi)
  all_goals exact stock_good a b c d ha hb hc hd _ _ i hi

private theorem bank_masses (a b c d v p : ℕ) (strict : Bool)
    (hv : v<2^(c-1)) (hp : p<2^(c-1))
    (hsub : ∀ e<c-1,p.testBit e=true → v.testBit e=true)
    (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4,∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    let C:=fun r : Fin 4 => (full a b c d r:ℤ)
    (fun r => ((banks a b c d v p strict r).map f).sum)=
      ![C 0*F 0,(if strict then C 3*F 3 else C 2*F 2)+(p:ℤ)*F 1,
        (if strict then C 2*F 2 else C 3*F 3)+((v:ℤ)-p)*F 1,(C 1-v)*F 1] := by
  dsimp only
  have hfull (r : Fin 4) : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full];have := Nat.two_pow_pos (chainLength a b c d r-1);omega
  have mU:=stock_mass a b c d 0 _ (hfull 0) f F hf
  have mW:=stock_mass a b c d 2 _ (hfull 2) f F hf
  have mX:=stock_mass a b c d 3 _ (hfull 3) f F hf
  have mV:=stock_mass a b c d 1 v (by simpa [chainLength] using hv) f F hf
  have mP:=stock_mass a b c d 1 p (by simpa [chainLength] using hp) f F hf
  have mC:=complement_mass a b c d 1 v (by simpa [chainLength] using hv) f F hf
  have mR : ((stock a b c d 1 (v ^^^ p)).map f).sum=((v:ℤ)-p)*F 1 := by
    have hs:=((v_split a b c d v p hsub).map f).sum_eq
    simp only [List.map_append,List.sum_append,mP,mV] at hs
    nlinarith only [hs]
  funext r
  cases strict <;> fin_cases r <;> dsimp [banks]
  all_goals simp only [List.map_append,List.sum_append,mU,mW,mX,mP,mR,mC]

private theorem literal_ear (a b c d v p : ℕ) (strict early : Bool) :
    blocksWord (withEar (size a b c d) (earSlot early) (packets a b c d v p strict))=
      insertAt (size a b c d) (word a b c d v p strict) (cut a b c d v p strict early) := by
  have split : word a b c d v p strict=
      preEar a b c d v p strict early++postEar a b c d v p strict early := by
    cases early <;> simp [word,packets,blocksWord,preEar,postEar,List.append_assoc]
  have marked : blocksWord (withEar (size a b c d) (earSlot early) (packets a b c d v p strict))=
      preEar a b c d v p strict early++size a b c d::postEar a b c d v p strict early := by
    cases early <;> simp [earSlot,withEar,packets,blocksWord,preEar,postEar,List.append_assoc]
  rw [marked,split]
  simp [cut,insertAt]

private theorem cut_bound (a b c d v p : ℕ) (strict early : Bool)
    (hp : (word a b c d v p strict).Perm (List.range (size a b c d))) :
    cut a b c d v p strict early<size a b c d := by
  have hl:=hp.length_eq
  have split : word a b c d v p strict=
      preEar a b c d v p strict early++postEar a b c d v p strict early := by
    cases early <;> simp [word,packets,blocksWord,preEar,postEar,List.append_assoc]
  rw [split] at hl
  have hpost : 0<(postEar a b c d v p strict early).length := by cases early <;> simp [postEar]
  simp only [List.length_append,List.length_range] at hl
  dsimp [cut]
  omega

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
