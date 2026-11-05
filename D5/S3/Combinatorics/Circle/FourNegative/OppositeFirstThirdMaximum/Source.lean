/- GID: D5/S3/Combinatorics/Circle/FourNegative/OppositeFirstThirdMaximum/Source
   generality: I
   mirror-B: none(waiver:private-consumed-endpoint-implementation)
   mirror-E: none(waiver:private-consumed-endpoint-implementation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Original physical opposite-maximum banks, exact inventory, masses and literal ear. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
namespace D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open SourceWidth PeriodicShortening RunFirstEarTransport
open private full stock complement stock_split canonical_inventory stock_good stock_mass complement_mass
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private size sourceMod base newBase charge oldValue newValue chainLength chainStart
  nextBase nextNewBase negatives chainOf chain_index chain_values source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private native_masses from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private insertAt from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

private def vMask (a b : ℕ) : ℕ := 2^(a-b-1)
private def rawBanks (a b d m : ℕ) : Fin 4 → List ℕ :=
  ![stock a b a d 0 (full a b a d 0)++stock a b a d 3 m,
    complement a b a d 3 m,
    stock a b a d 2 (full a b a d 2)++stock a b a d 1 (vMask a b),
    complement a b a d 1 (vMask a b)]
private def banks (a b d m : ℕ) (early : Bool) : Fin 4 → List ℕ :=
  if early then rawBanks a b d m
  else ![rawBanks a b d m 2,rawBanks a b d m 3,rawBanks a b d m 0,rawBanks a b d m 1]
private def terminals (a b d : ℕ) (early : Bool) : Fin 4 → ℕ :=
  if early then ![a+b+a+d-1,d-1,d+a-1,d+a+b-1]
  else ![d+a-1,d+a+b-1,a+b+a+d-1,d-1]
private def word (a b d m : ℕ) (early : Bool) : List ℕ :=
  let P:=banks a b d m early
  let T:=terminals a b d early
  P 0++T 0::P 1++T 1::P 2++T 2::P 3++[T 3]
private def beforeEar (a b d m : ℕ) (early : Bool) : List ℕ :=
  let P:=banks a b d m early
  let T:=terminals a b d early
  if early then P 0++[T 0]
  else P 0++[T 0]++P 1++[T 1]++P 2++[T 2]
private def afterEar (a b d m : ℕ) (early : Bool) : List ℕ :=
  let P:=banks a b d m early
  let T:=terminals a b d early
  if early then P 1++T 1::P 2++T 2::P 3++[T 3]
  else P 3++[T 3]
private def freshCut (a b d m : ℕ) (early : Bool) : ℕ := (beforeEar a b d m early).length
private def newBanks (a b d m : ℕ) (early : Bool) : Fin 4 → List ℕ :=
  let P:=banks a b d m early
  if early then ![P 0,size a b a d::P 1,P 2,P 3]
  else ![P 0,P 1,P 2,size a b a d::P 3]
private def enlarged (a b d m : ℕ) (early : Bool) : List ℕ :=
  let P:=newBanks a b d m early
  let T:=terminals a b d early
  P 0++T 0::P 1++T 1::P 2++T 2::P 3++[T 3]

private theorem inventory (a b d m : ℕ) (early : Bool)
    (ha : 2≤a) (hb : 2≤b) (hd : 2≤d) :
    (word a b d m early).Perm (List.range (size a b a d)) := by
  have hv:=Multiset.coe_eq_coe.mpr (stock_split a b a d 1 (vMask a b))
  have hx:=Multiset.coe_eq_coe.mpr (stock_split a b a d 3 m)
  simp only [←Multiset.coe_add] at hv hx
  apply Multiset.coe_eq_coe.mp
  change (word a b d m early : Multiset ℕ)=(List.range (a+b+a+d) : Multiset ℕ)
  rw [←canonical_inventory a b a d ha hb ha hd]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  rw [←hv,←hx]
  have cons_coe (i : ℕ) (xs : List ℕ) :
      ((i::xs : List ℕ) : Multiset ℕ)={i}+(xs : Multiset ℕ) := rfl
  cases early <;> dsimp [word,banks,rawBanks,terminals]
  all_goals simp only [cons_coe,←Multiset.coe_add,Multiset.coe_singleton]
  all_goals ac_rfl

private theorem banks_good (a b d m : ℕ) (early : Bool)
    (ha : 2≤a) (hb : 2≤b) (hd : 2≤d)
    (r : Fin 4) (i : ℕ) (hi : i∈banks a b d m early r) :
    i<size a b a d ∧ i∉negatives a b a d := by
  cases early <;> fin_cases r <;> dsimp [banks,rawBanks,complement] at hi
  all_goals try (simp only [List.mem_append] at hi; rcases hi with hi|hi)
  all_goals exact stock_good a b a d ha hb ha hd _ _ i hi

private theorem mask_cap (a b : ℕ) (hb : 2≤b) (hba : b<a) : vMask a b<2^(a-1) := by
  dsimp [vMask]
  exact Nat.pow_lt_pow_right (by decide : 1<2) (by omega)

private theorem raw_masses (a b d m : ℕ) (ha : 2≤a) (hb : 2≤b)
    (hba : b<a) (hm : m<2^(a-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b a d r-1,
      f (chainStart b a d r+e)=2^e*F r) :
    (fun r => ((rawBanks a b d m r).map f).sum)=
      ![(full a b a d 0:ℤ)*F 0+(m:ℤ)*F 3,
        ((full a b a d 3:ℤ)-m)*F 3,
        (full a b a d 2:ℤ)*F 2+(vMask a b:ℤ)*F 1,
        ((full a b a d 1:ℤ)-vMask a b)*F 1] := by
  have hfull (r : Fin 4) : full a b a d r<2^(chainLength a b a d r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b a d r-1); omega
  have hm' : m<2^(chainLength a b a d 3-1) := by simpa [chainLength] using hm
  have hn' : vMask a b<2^(chainLength a b a d 1-1) := by simpa [chainLength] using mask_cap a b hb hba
  have mu:=stock_mass a b a d 0 _ (hfull 0) f F hf
  have mx:=stock_mass a b a d 3 m hm' f F hf
  have nx:=complement_mass a b a d 3 m hm' f F hf
  have mw:=stock_mass a b a d 2 _ (hfull 2) f F hf
  have mv:=stock_mass a b a d 1 _ hn' f F hf
  have nv:=complement_mass a b a d 1 _ hn' f F hf
  funext r
  fin_cases r <;> dsimp [rawBanks] <;> try simp only [List.map_append,List.sum_append]
  · exact congrArg₂ (·+·) mu mx
  · exact nx
  · exact congrArg₂ (·+·) mw mv
  · exact nv

/-- Pointwise shared charge is nonnegative, including each of the four actual negative labels. -/
private theorem label_charge (a b d : ℕ) (ha : 2≤a) (hb : 2≤b) (hd : 2≤d)
    (i : ℕ) (hi : i<size a b a d) : 0≤2*oldValue a b a d i-newValue a b a d i := by
  let r:=chainOf b a d i
  let e:=i-chainStart b a d r
  obtain ⟨he,hel,hpositive⟩:=chain_index a b a d i ha hb ha hd hi
  change chainStart b a d r+e=i at he
  change e<chainLength a b a d r at hel
  have tab:=chain_values a b a d ha hb ha hd
  have hf:=tab.2.1 r e hel
  have hg:=tab.2.2.1 r e hel
  rw [he] at hf hg
  by_cases hp : e+1<chainLength a b a d r
  · rw [if_pos hp] at hf hg
    have hc (j : Fin 4) : 0≤charge b a j := by
      fin_cases j <;> simp [charge] <;> positivity
    rw [hf,hg]
    have heq : 2*(2^e*base a b a d r)-2^e*newBase a b a d r=
        2^e*charge b a r := by dsimp [newBase]; ring
    rw [heq]
    exact mul_nonneg (by positivity) (hc r)
  · have hei : chainStart b a d r+(chainLength a b a d r-1)=i := by omega
    have hn:=native_masses a b a d ha hb ha hd r
    dsimp only at hn
    rw [hei] at hn
    have hc (j : Fin 4) : 0≤2*nextBase a b a d j-nextNewBase a b a d j := by
      fin_cases j <;> dsimp [nextBase,nextNewBase,newBase,charge,base] <;> ring_nf <;> positivity
    nlinarith only [hn.2.2.1,hn.2.2.2,hc r]

private theorem word_split (a b d m : ℕ) (early : Bool) :
    word a b d m early=beforeEar a b d m early++afterEar a b d m early := by
  cases early <;> simp [word,beforeEar,afterEar,List.append_assoc]
private theorem literal_ear (a b d m : ℕ) (early : Bool) :
    insertAt (size a b a d) (word a b d m early) (freshCut a b d m early)=
      enlarged a b d m early := by
  rw [word_split]
  change insertAt (size a b a d)
    (beforeEar a b d m early++afterEar a b d m early)
    ((beforeEar a b d m early).length+0)=_
  unfold insertAt
  rw [List.take_length_add_append,List.drop_length_add_append]
  cases early <;> simp [enlarged,newBanks,beforeEar,afterEar,List.append_assoc]
private theorem cut_bound (a b d m : ℕ) (early : Bool)
    (ha : 2≤a) (hb : 2≤b) (hd : 2≤d) : freshCut a b d m early≤size a b a d := by
  have hl:=(inventory a b d m early ha hb hd).length_eq
  rw [word_split] at hl
  simp only [List.length_append,List.length_range] at hl
  dsimp [freshCut]
  omega

end D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum
