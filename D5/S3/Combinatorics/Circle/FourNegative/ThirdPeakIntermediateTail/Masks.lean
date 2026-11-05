/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakIntermediateTail/Masks
   generality: I
   mirror-B: none(waiver:private-consumed-native-masks)
   mirror-E: none(waiver:private-consumed-native-masks)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Literal binary supports, disjoint inventories, exact popcounts and ear cuts. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks

/-! A bit list is an actual list of exponents of
original physical labels. Its mask is the natural sum of those distinct powers.
Binary-sum injectivity proves its native bitIndices, so its length is a genuine
popcount. No capacity or numerical stock is substituted for a physical subset. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail
open scoped BigOperators
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private size negatives chainLength chainStart
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private canonical_inventory stock full
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

private def branch (a b d : ℕ) : Fin 4 → Prop :=
  ![d=a ∧ d+2≤b, a<d ∧ d+2≤b, a<d ∧ b=d+1, d=a ∧ b=d+1]
private def route (a b d : ℕ) : Fin 4 :=
  if d+2≤b then (if d=a then 0 else 1) else (if a<d then 2 else 3)
private theorem route_valid (a b d : ℕ) (had : a≤d) (hdb : d<b) :
    branch a b d (route a b d) := by
  unfold route
  split_ifs <;> simp only [branch] <;> constructor <;> omega

private def bitRange (lo hi : ℕ) : List ℕ := List.range' lo (hi-lo)
private theorem bitRange_mem (lo hi e : ℕ) : e∈bitRange lo hi ↔ lo≤e ∧ e<hi := by
  simp only [bitRange,List.mem_range',Nat.one_mul]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨hl,hh⟩; exact ⟨e-lo,by omega,by omega⟩
private theorem bitRange_join (l m n : ℕ) (hlm : l≤m) (hmn : m≤n) :
    bitRange l m++bitRange m n=bitRange l n := by
  dsimp [bitRange]
  have he : l+(m-l)=m := by omega
  have he' : m-l+(n-m)=n-l := by omega
  simpa only [he,he'] using (List.range'_append_1 (s:=l) (m:=m-l) (n:=n-m))
private theorem bitRange_one (n : ℕ) : bitRange n (n+1)=[n] := by simp [bitRange]
private theorem bitRange_zero (n : ℕ) : bitRange 0 n=List.range n := by
  simp [bitRange,List.range_eq_range']

private def vbits (mode : Fin 4) (b c : ℕ) : Fin 4 → List ℕ :=
  let g:=c-b
  ![bitRange g (c-1),[],if mode=0 ∨ mode=1 then [] else [g-1],
    bitRange 0 (if mode=0 ∨ mode=1 then g else g-1)]
private def wbits (mode : Fin 4) (a b d : ℕ) : Fin 4 → List ℕ :=
  let al:=d-a
  let be:=b-d
  if mode=0 then ![[],[be-2]++bitRange be (b-1),[],bitRange 0 (be-2)++[be-1]]
  else if mode=1 then ![[],bitRange (al+be-1) (b-1),
    [be-2]++bitRange be (al+be-1),bitRange 0 (be-2)++[be-1]]
  else if mode=2 then ![[],bitRange al (b-1),bitRange 1 al,[0]]
  else ![[],bitRange 1 (b-1),[],[0]]

private theorem v_inventory (mode : Fin 4) (b c : ℕ) (hb : 2≤b) (hbc : b<c) :
    (vbits mode b c 0++vbits mode b c 2++vbits mode b c 3).Perm (List.range (c-1)) := by
  let g:=c-b
  have hg : 1≤g ∧ g≤c-1 := by dsimp [g]; omega
  have full : bitRange 0 g++bitRange g (c-1)=List.range (c-1) := by
    rw [bitRange_join 0 g (c-1) (by omega) (by omega),bitRange_zero]
  have low : bitRange 0 (g-1)++[g-1]=bitRange 0 g := by
    rw [←bitRange_one (g-1)]
    have he : g-1+1=g := by omega
    rw [he,bitRange_join 0 (g-1) g (by omega) (by omega)]
  have ordered : (bitRange g (c-1)++bitRange 0 g).Perm (List.range (c-1)) := by
    rw [←full]
    exact List.perm_append_comm
  have lower : ([g-1]++bitRange 0 (g-1)).Perm (bitRange 0 g) := by
    rw [←low]
    exact List.perm_append_comm
  have adjacent : (bitRange g (c-1)++[g-1]++bitRange 0 (g-1)).Perm
      (List.range (c-1)) := by
    simpa only [List.append_assoc] using
      (lower.append_left (bitRange g (c-1))).trans ordered
  fin_cases mode
  · simpa [vbits,g] using ordered
  · simpa [vbits,g] using ordered
  · simpa [vbits,g] using adjacent
  · simpa [vbits,g] using adjacent

private theorem w_inventory (mode : Fin 4) (a b d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hm : branch a b d mode) :
    (wbits mode a b d 1++wbits mode a b d 2++wbits mode a b d 3).Perm
      (List.range (b-1)) := by
  let al:=d-a
  let be:=b-d
  have hal : al+a=d := by dsimp [al]; omega
  have hbe : be+d=b := by dsimp [be]; omega
  fin_cases mode <;> simp [branch,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq] at hm
  · have hb : 2≤be ∧ be≤b-1 := by dsimp [be]; omega
    have full : (bitRange 0 (be-2)++[be-2]++[be-1])++bitRange be (b-1)=
        List.range (b-1) := by
      rw [←bitRange_one (be-2),show be-2+1=be-1 by omega,
        bitRange_join 0 (be-2) (be-1) (by omega) (by omega),
        ←bitRange_one (be-1),show be-1+1=be by omega,
        bitRange_join 0 (be-1) be (by omega) (by omega),
        bitRange_join 0 be (b-1) (by omega) (by omega),bitRange_zero]
    apply Multiset.coe_eq_coe.mp
    rw [←full]
    norm_num [wbits,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq,Matrix.vecHead,Matrix.vecTail,Fin.reduceEq,ite_false,ite_true,List.append_nil]
    apply Multiset.coe_eq_coe.mp
    simp only [←Multiset.cons_coe,←Multiset.singleton_add,←Multiset.coe_add,Multiset.coe_singleton,Multiset.coe_nil,add_zero]
    dsimp only [be]
    ac_rfl
  · have hb : 2≤be ∧ be≤al+be-1 ∧ al+be-1≤b-1 := by dsimp [al,be]; omega
    have full : (bitRange 0 (be-2)++[be-2]++[be-1])++
        bitRange be (al+be-1)++bitRange (al+be-1) (b-1)=List.range (b-1) := by
      rw [←bitRange_one (be-2),show be-2+1=be-1 by omega,
        bitRange_join 0 (be-2) (be-1) (by omega) (by omega),
        ←bitRange_one (be-1),show be-1+1=be by omega,
        bitRange_join 0 (be-1) be (by omega) (by omega),
        bitRange_join 0 be (al+be-1) (by omega) (by omega),
        bitRange_join 0 (al+be-1) (b-1) (by omega) (by omega),bitRange_zero]
    apply Multiset.coe_eq_coe.mp
    rw [←full]
    norm_num [wbits,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq,Matrix.vecHead,Matrix.vecTail,Fin.reduceEq,ite_false,ite_true]
    apply Multiset.coe_eq_coe.mp
    simp only [←Multiset.cons_coe,←Multiset.singleton_add,←Multiset.coe_add,Multiset.coe_singleton,Multiset.coe_nil,add_zero]
    dsimp only [al,be]
    ac_rfl
  · have hal' : 1≤al ∧ al≤b-1 := by dsimp [al]; omega
    have full : [0]++bitRange 1 al++bitRange al (b-1)=List.range (b-1) := by
      rw [←bitRange_one 0,bitRange_join 0 1 al (by omega) (by omega),
        bitRange_join 0 al (b-1) (by omega) (by omega),bitRange_zero]
    apply Multiset.coe_eq_coe.mp
    rw [←full]
    norm_num [wbits,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq,Matrix.vecHead,Matrix.vecTail,Fin.reduceEq,ite_false,ite_true]
    apply Multiset.coe_eq_coe.mp
    simp only [←Multiset.cons_coe,←Multiset.singleton_add,←Multiset.coe_add,Multiset.coe_singleton,Multiset.coe_nil,add_zero]
    dsimp only [al]
    ac_rfl
  · have full : [0]++bitRange 1 (b-1)=List.range (b-1) := by
      rw [←bitRange_one 0,bitRange_join 0 1 (b-1) (by omega) (by omega),bitRange_zero]
    apply Multiset.coe_eq_coe.mp
    rw [←full]
    norm_num [wbits,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq,Matrix.vecHead,Matrix.vecTail,Fin.reduceEq,ite_false,ite_true,List.append_nil]

private def maskOf (l : List ℕ) : ℕ := (l.map (fun e => 2^e)).sum
private def popcount (m : ℕ) : ℕ := m.bitIndices.toFinset.card
private theorem maskOf_append (l r : List ℕ) : maskOf (l++r)=maskOf l+maskOf r := by
  simp [maskOf]
private theorem maskOf_range (n : ℕ) : maskOf (List.range n)+1=2^n := by
  induction n with
  | zero => simp [maskOf]
  | succ n ih =>
    rw [List.range_succ,maskOf_append]
    simp only [maskOf,List.map_singleton,List.sum_singleton,pow_succ]
    change maskOf (List.range n)+2^n+1=2^n*2
    omega
private theorem native_bits (l : List ℕ) (hn : l.Nodup) :
    (maskOf l).bitIndices.toFinset=l.toFinset := by
  apply Finset.geomSum_injective (by decide : 2≤(2:ℕ))
  change (∑ e ∈ (maskOf l).bitIndices.toFinset, (2:ℕ)^e) =
    ∑ e ∈ l.toFinset, (2:ℕ)^e
  rw [Finset.sum_toFinset_bitIndices_two_pow]
  exact (List.sum_toFinset (fun e : ℕ => 2^e) hn).symm

-- This certificate has no assumed feasibility fields: its constructor is fed
-- by the actual disjoint interval inventories above.
private structure NativePartition (len : ℕ) (l0 l1 l2 : List ℕ) : Prop where
  physical : (l0++l1++l2).Perm (List.range len)
  fits : maskOf l0<2^len ∧ maskOf l1<2^len ∧ maskOf l2<2^len
  supports : (maskOf l0).bitIndices.toFinset=l0.toFinset ∧
    (maskOf l1).bitIndices.toFinset=l1.toFinset ∧
    (maskOf l2).bitIndices.toFinset=l2.toFinset
  disjoint : Disjoint (maskOf l0).bitIndices.toFinset (maskOf l1).bitIndices.toFinset ∧
    Disjoint (maskOf l0).bitIndices.toFinset (maskOf l2).bitIndices.toFinset ∧
    Disjoint (maskOf l1).bitIndices.toFinset (maskOf l2).bitIndices.toFinset
  fullSupport : ((maskOf l0).bitIndices.toFinset ∪ (maskOf l1).bitIndices.toFinset) ∪
    (maskOf l2).bitIndices.toFinset=Finset.range len
  counts : popcount (maskOf l0)=l0.length ∧ popcount (maskOf l1)=l1.length ∧
    popcount (maskOf l2)=l2.length
  splitXor : maskOf (l1++l2) ^^^ maskOf l2=maskOf l1

private theorem native_partition (len : ℕ) (l0 l1 l2 : List ℕ)
    (hp : (l0++l1++l2).Perm (List.range len)) : NativePartition len l0 l1 l2 := by
  classical
  have hn:=hp.nodup_iff.mpr List.nodup_range
  simp only [List.nodup_append] at hn
  have hn0 : l0.Nodup := by tauto
  have hn1 : l1.Nodup := by tauto
  have hn2 : l2.Nodup := by tauto
  have b0:=native_bits l0 hn0
  have b1:=native_bits l1 hn1
  have b2:=native_bits l2 hn2
  have hs:=((hp.map (fun e : ℕ => 2^e)).sum_eq)
  change maskOf (l0++l1++l2)=maskOf (List.range len) at hs
  rw [maskOf_append,maskOf_append] at hs
  have hf:=maskOf_range len
  refine ⟨hp,by omega,⟨b0,b1,b2⟩,?_,?_,?_,?_⟩
  · rw [b0,b1,b2]
    have dd (l r : List ℕ) (h : List.Disjoint l r) : Disjoint l.toFinset r.toFinset := by
      apply Finset.disjoint_left.mpr
      intro e he hr
      exact List.disjoint_left.mp h (List.mem_toFinset.mp he) (List.mem_toFinset.mp hr)
    exact ⟨dd l0 l1 (by
        intro e he0 he1
        exact hn.1.2.2 e he0 e he1 rfl),
      dd l0 l2 (by
        intro e he0 he2
        exact hn.2.2 e (by simp [he0]) e he2 rfl),
      dd l1 l2 (by
        intro e he1 he2
        exact hn.2.2 e (by simp [he1]) e he2 rfl)⟩
  · rw [b0,b1,b2]
    have he : (l0++l1++l2).toFinset=(List.range len).toFinset := List.toFinset_eq_of_perm _ _ hp
    simpa only [List.toFinset_append,List.toFinset_range,Finset.union_assoc] using he
  · simp [popcount,b0,b1,b2,List.toFinset_card_of_nodup hn0,
      List.toFinset_card_of_nodup hn1,List.toFinset_card_of_nodup hn2]
  · have hn12 : (l1++l2).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hn1,hn2,?_⟩
      intro e he1 f hf
      exact hn.2.2 e (by simp [he1]) f hf
    have bb:=native_bits (l1++l2) hn12
    have hdis : List.Disjoint l1 l2 := by
      intro e he1 he2
      exact hn.2.2 e (by simp [he1]) e he2 rfl
    have hx : (maskOf (l1++l2) ^^^ maskOf l2).bitIndices.toFinset=l1.toFinset := by
      ext e
      have hu : (maskOf (l1++l2)).testBit e=true ↔ e∈l1.toFinset ∪ l2.toFinset := by
        rw [←List.toFinset_append,←bb]
        simp only [List.mem_toFinset,Nat.mem_bitIndices]
      have hv : (maskOf l2).testBit e=true ↔ e∈l2.toFinset := by
        rw [←b2]
        simp only [List.mem_toFinset,Nat.mem_bitIndices]
      have hd : ¬ (e∈l1.toFinset ∧ e∈l2.toFinset) := by
        rintro ⟨he,hf⟩
        exact List.disjoint_left.mp hdis (List.mem_toFinset.mp he) (List.mem_toFinset.mp hf)
      simp only [Finset.mem_union] at hu
      simp only [List.mem_toFinset,Nat.mem_bitIndices,Nat.testBit_xor]
      cases u : (maskOf (l1++l2)).testBit e <;> cases v : (maskOf l2).testBit e <;> simp_all
    have he:=congrArg (fun S : Finset ℕ => ∑ e∈S,(2:ℕ)^e) hx
    rw [Finset.sum_toFinset_bitIndices_two_pow] at he
    exact he.trans (List.sum_toFinset (fun e : ℕ => 2^e) hn1)

private theorem native_inventories (mode : Fin 4) (a b c d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hbc : b<c) (hm : branch a b d mode) :
    NativePartition (c-1) (vbits mode b c 0) (vbits mode b c 2) (vbits mode b c 3) ∧
    NativePartition (b-1) (wbits mode a b d 1) (wbits mode a b d 2) (wbits mode a b d 3) := by
  exact ⟨native_partition _ _ _ _ (v_inventory mode b c (by omega) hbc),
    native_partition _ _ _ _ (w_inventory mode a b d ha had hdb hm)⟩

private def shift (off : ℕ) (l : List ℕ) : List ℕ := l.map (off+·)
private theorem shift_range (off n : ℕ) : shift off (List.range n)=List.range' off n := by
  simpa only [shift,List.range_eq_range',Nat.add_zero] using (List.map_add_range' (a:=off) 0 n 1)
private def banks (mode : Fin 4) (a b c d : ℕ) : Fin 4 → List ℕ :=
  let V:=vbits mode b c
  let W:=wbits mode a b d
  ![shift d (V 0),shift (d+c) (W 1),
    shift d (V 2)++shift (d+c) (W 2)++List.range' (d+c+b) (a-1),
    List.range (d-1)++shift d (V 3)++shift (d+c) (W 3)]
private def terminals (a b c d : ℕ) : Fin 4 → ℕ :=
  ![d+c-1,d+c+b-1,a+b+c+d-1,d-1]
private def word (mode : Fin 4) (a b c d : ℕ) : List ℕ :=
  let P:=banks mode a b c d
  let T:=terminals a b c d
  P 0++[T 0]++P 1++[T 1]++P 2++[T 2]++P 3++[T 3]
private def freshCut (a b d : ℕ) : ℕ := if d=a ∧ b=d+1 then b else a+b+1
private def before (mode : Fin 4) (a b c d : ℕ) : List ℕ :=
  let P:=banks mode a b c d
  let T:=terminals a b c d
  if mode=3 then P 0++[T 0] else P 0++[T 0]++P 1++[T 1]
private def after (mode : Fin 4) (a b c d : ℕ) : List ℕ :=
  let P:=banks mode a b c d
  let T:=terminals a b c d
  if mode=3 then P 1++[T 1]++P 2++[T 2]++P 3++[T 3]
  else P 2++[T 2]++P 3++[T 3]

private theorem banks_inventory (mode : Fin 4) (a b c d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hbc : b<c) (hm : branch a b d mode) :
    (word mode a b c d).Perm (List.range (size a b c d)) := by
  have native:=native_inventories mode a b c d ha had hdb hbc hm
  have hv:=(native.1.physical.map (d+·))
  have hw:=(native.2.physical.map (d+c+·))
  change (shift d (vbits mode b c 0++vbits mode b c 2++vbits mode b c 3)).Perm
    (shift d (List.range (c-1))) at hv
  change (shift (d+c) (wbits mode a b d 1++wbits mode a b d 2++wbits mode a b d 3)).Perm
    (shift (d+c) (List.range (b-1))) at hw
  simp only [shift,List.map_append] at hv hw
  have hv':=Multiset.coe_eq_coe.mpr hv
  have hw':=Multiset.coe_eq_coe.mpr hw
  have full':=(canonical_inventory a b c d ha (by omega) (by omega) (by omega))
  simp only [stock,full,chamberLabels_full,chainLength,chainStart,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Matrix.cons_val_zero',Matrix.cons_val_succ'] at full'
  simp only [←List.range_eq_range'] at full'
  apply Multiset.coe_eq_coe.mp
  dsimp only [size]
  rw [←full']
  rw [←shift_range d (c-1),←shift_range (d+c) (b-1)]
  simp only [shift] at *
  simp only [←Multiset.coe_add,Multiset.coe_singleton] at hv' hw' ⊢
  rw [←hv',←hw']
  dsimp [word,banks,terminals,shift]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  ac_rfl

private theorem banks_good (mode : Fin 4) (a b c d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hbc : b<c) (hm : branch a b d mode)
    (i : Fin 4) (e : ℕ) (he : e∈banks mode a b c d i) :
    e<size a b c d ∧ e∉negatives a b c d := by
  have native:=native_inventories mode a b c d ha had hdb hbc hm
  have vfit (j : Fin 4) (t : ℕ) (ht : t∈vbits mode b c j) : t<c-1 := by
    have hv:=native.1.physical
    apply List.mem_range.mp
    apply hv.mem_iff.mp
    fin_cases j
    · simp only [List.mem_append]; exact Or.inl (Or.inl (by simpa using ht))
    · simpa [vbits] using ht
    · simp only [List.mem_append]; exact Or.inl (Or.inr (by simpa using ht))
    · simp only [List.mem_append]; exact Or.inr (by simpa using ht)
  have wfit (j : Fin 4) (t : ℕ) (ht : t∈wbits mode a b d j) : t<b-1 := by
    have hw:=native.2.physical
    apply List.mem_range.mp
    apply hw.mem_iff.mp
    fin_cases j
    · fin_cases mode <;> simpa [wbits] using ht
    · simp only [List.mem_append]; exact Or.inl (Or.inl (by simpa using ht))
    · simp only [List.mem_append]; exact Or.inl (Or.inr (by simpa using ht))
    · simp only [List.mem_append]; exact Or.inr (by simpa using ht)
  have sv (j : Fin 4) (he : e∈shift d (vbits mode b c j)) :
      e<size a b c d ∧ e∉negatives a b c d := by
    obtain ⟨t,ht,rfl⟩:=List.mem_map.mp he
    have hf:=vfit j t ht
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    omega
  have sw (j : Fin 4) (he : e∈shift (d+c) (wbits mode a b d j)) :
      e<size a b c d ∧ e∉negatives a b c d := by
    obtain ⟨t,ht,rfl⟩:=List.mem_map.mp he
    have hf:=wfit j t ht
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    omega
  have su (he : e∈List.range (d-1)) : e<size a b c d ∧ e∉negatives a b c d := by
    have hf:=List.mem_range.mp he
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    omega
  have sx (he : e∈List.range' (d+c+b) (a-1)) :
      e<size a b c d ∧ e∉negatives a b c d := by
    obtain ⟨t,ht,rfl⟩:=List.mem_range'.mp he
    simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    omega
  fin_cases i <;> simp only [banks,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ'] at he
  · exact sv 0 he
  · exact sw 1 he
  · simp only [List.mem_append] at he
    rcases he with (h | h) | h
    · exact sv 2 h
    · exact sw 2 h
    · exact sx h
  · simp only [List.mem_append] at he
    rcases he with (h | h) | h
    · exact su h
    · exact sv 3 h
    · exact sw 3 h

private theorem native_popcounts (mode : Fin 4) (a b c d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hbc : b<c) (hm : branch a b d mode) :
    (fun i : Fin 4 => popcount (maskOf (vbits mode b c i)))=
      ![b-1,0,if mode=0 ∨ mode=1 then 0 else 1,
        if mode=0 ∨ mode=1 then c-b else c-b-1] ∧
    (fun i : Fin 4 => popcount (maskOf (wbits mode a b d i)))=
      ![0,if mode=3 then a-1 else a,
        if mode=0 ∨ mode=3 then 0 else if mode=1 then d-a else d-a-1,
        if mode=0 ∨ mode=1 then b-d-1 else 1] := by
  have native:=native_inventories mode a b c d ha had hdb hbc hm
  constructor
  · funext i
    fin_cases i
    · refine native.1.counts.1.trans ?_
      simp [vbits,bitRange,Matrix.cons_val_zero',Matrix.cons_val_succ']
      omega
    · simp [vbits,Matrix.cons_val_zero',Matrix.cons_val_succ',popcount,maskOf]
    · refine native.1.counts.2.1.trans ?_
      simp [vbits,bitRange,Matrix.cons_val_zero',Matrix.cons_val_succ']
      split_ifs <;> simp_all
    · refine native.1.counts.2.2.trans ?_
      simp [vbits,bitRange,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · funext i
    fin_cases i
    · fin_cases mode <;> simp [wbits,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq,popcount,maskOf]
    · refine native.2.counts.1.trans ?_
      fin_cases mode <;> simp [branch,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq] at hm
      all_goals simp [wbits,bitRange,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq] <;> omega
    · refine native.2.counts.2.1.trans ?_
      fin_cases mode <;> simp [branch,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq] at hm
      all_goals simp [wbits,bitRange,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq] <;> omega
    · refine native.2.counts.2.2.trans ?_
      fin_cases mode <;> simp [branch,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq] at hm
      all_goals simp [wbits,bitRange,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq] <;> omega

private theorem bank_lengths (mode : Fin 4) (a b c d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hbc : b<c) (hm : branch a b d mode) :
    (fun i : Fin 4 => (banks mode a b c d i).length+1)=
      (if mode=3 then ![b,a,a+1,c-1] else ![b,a+1,d,c-1]) := by
  have native:=native_inventories mode a b c d ha had hdb hbc hm
  have counts:=native_popcounts mode a b c d ha had hdb hbc hm
  have vl (i : Fin 4) : (vbits mode b c i).length=
      (![b-1,0,if mode=0 ∨ mode=1 then 0 else 1,
        if mode=0 ∨ mode=1 then c-b else c-b-1] : Fin 4→ℕ) i := by
    fin_cases i
    · exact native.1.counts.1.symm.trans (congrFun counts.1 0)
    · simp [vbits]
    · exact native.1.counts.2.1.symm.trans (congrFun counts.1 2)
    · exact native.1.counts.2.2.symm.trans (congrFun counts.1 3)
  have wl (i : Fin 4) : (wbits mode a b d i).length=
      (![0,if mode=3 then a-1 else a,
        if mode=0 ∨ mode=3 then 0 else if mode=1 then d-a else d-a-1,
        if mode=0 ∨ mode=1 then b-d-1 else 1] : Fin 4→ℕ) i := by
    fin_cases i
    · fin_cases mode <;> simp [wbits]
    · exact native.2.counts.1.symm.trans (congrFun counts.2 1)
    · exact native.2.counts.2.1.symm.trans (congrFun counts.2 2)
    · exact native.2.counts.2.2.symm.trans (congrFun counts.2 3)
  funext i
  fin_cases i <;> simp only [banks,shift,List.length_map,List.length_append,
    List.length_range,List.length_range',vl,wl,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals fin_cases mode <;> simp [branch,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq] at hm
  all_goals norm_num [Fin.reduceEq,ite_true,ite_false,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  all_goals omega

private theorem literal_cut (mode : Fin 4) (a b c d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hbc : b<c) (hm : branch a b d mode) :
    (before mode a b c d).length=freshCut a b d ∧ freshCut a b d<size a b c d ∧
    word mode a b c d=before mode a b c d++after mode a b c d ∧
    insertAt (size a b c d) (word mode a b c d) (freshCut a b d)=
      before mode a b c d++size a b c d::after mode a b c d := by
  have hl:=bank_lengths mode a b c d ha had hdb hbc hm
  have h0:=congrFun hl 0
  have h1:=congrFun hl 1
  have hsplit : word mode a b c d=before mode a b c d++after mode a b c d := by
    fin_cases mode <;> simp [word,before,after,List.append_assoc]
  have hlen : (before mode a b c d).length=freshCut a b d := by
    fin_cases mode <;> simp [branch,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq] at hm
    all_goals simp [Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq,
      Matrix.vecHead,Matrix.vecTail,Function.comp_apply] at h0 h1
    all_goals simp [before,Fin.mk.injEq,List.length_append]
    all_goals dsimp only [freshCut]
    all_goals split_ifs <;> omega
  refine ⟨hlen,by dsimp [freshCut,size]; split_ifs <;> omega,hsplit,?_⟩
  rw [hsplit,←hlen]
  simp [insertAt]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail
