/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/DescendingSource
   generality: I
   mirror-B: none(waiver:private-consumed-construction)
   mirror-E: none(waiver:private-consumed-construction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Descending source for the physical first-peak joint lift. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.DescendingCharts
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

/-! DescendingSource for the paired physical source construction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Descending
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private mask_complement from D5.S3.Combinatorics.Circle.ThreeBitSource
open private size sourceMod base newBase chainLength chainStart oldValue newValue
  chain_values negatives source_signs
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

/- Both the numeric complement identity and the disjoint physical-bit partition. -/
private theorem mask_data (e r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ 2 ^ e) :
    (2 ^ e-r) + (r-1)=2 ^ e-1 ∧ 
    Disjoint (2 ^ e-r).bitIndices.toFinset (r-1).bitIndices.toFinset ∧ 
    (2 ^ e-r).bitIndices.toFinset ∪ (r-1).bitIndices.toFinset=Finset.range e := by
  have he : (2 ^ e-r) + (r-1)=2 ^ e-1 := by omega
  exact ⟨he,mask_complement e (2 ^ e-r) (r-1) he⟩

private theorem low_split (e off r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ 2 ^ e) :
    (chamberLabels e off (2 ^ e-r) ++ chamberLabels e off (r-1)).Perm
      (List.range' off e) := by
  have hd := mask_data e r hr hrn
  have mem_bit (m i : ℕ) : i∈m.bitIndices.toFinset ↔ m.testBit i=true := by
    simp only [List.mem_toFinset,Nat.mem_bitIndices]
  apply (List.perm_ext_iff_of_nodup ?_ (List.nodup_range' (s:=off) (n:=e))).mpr
  · intro i
    simp only [List.mem_append,chamberLabels_mem,List.mem_range']
    constructor
    · rintro (⟨j,hj,_,hji⟩|⟨j,hj,_,hji⟩)
      all_goals exact ⟨j,hj,by omega⟩
    · rintro ⟨j,hj,hij⟩
      have hmem : j∈(2 ^ e-r).bitIndices.toFinset ∪ (r-1).bitIndices.toFinset := by
        rw [hd.2.2]
        exact Finset.mem_range.mpr hj
      rcases Finset.mem_union.mp hmem with hp|hq
      · exact Or.inl ⟨j,hj,(mem_bit _ _).mp hp,by omega⟩
      · exact Or.inr ⟨j,hj,(mem_bit _ _).mp hq,by omega⟩
  · apply List.nodup_append.mpr
    refine ⟨chamberLabels_nodup _ _ _,chamberLabels_nodup _ _ _,?_⟩
    intro i hi j hj hij
    obtain ⟨u,hu,hbu,hui⟩ := (chamberLabels_mem _ _ _ _).mp hi
    obtain ⟨v,hv,hbv,hvj⟩ := (chamberLabels_mem _ _ _ _).mp hj
    have huv : u=v := by omega
    subst v
    exact Finset.disjoint_left.mp hd.2.1 ((mem_bit _ _).mpr hbu) ((mem_bit _ _).mpr hbv)


private def bank (corner : Bool) (a b c d r v : ℕ) : Fin 4 → List ℕ :=
  let e := a-d
  let n := 2 ^ e
  let off := d + c + b
  let X := List.range' (off + e) (a-1-e)
  let U := chamberLabels (d-1) 0 ((2 ^ (d-1)-1) ^^^ v)
  let V := List.range' d (c-1)
  let W := List.range' (d + c) (b-1) ++ chamberLabels e off (r-1)
  let p := chamberLabels e off (n-r)
  let bit := chamberLabels (d-1) 0 v
  if corner then ![X,U ++ p,V ++ bit,W] else ![X,V ++ p ++ bit,U,W]

private def terminal (corner : Bool) (a b c d : ℕ) : Fin 4 → ℕ :=
  if corner then ![a + b + c + d-1,d-1,d + c-1,d + c + b-1]
  else ![a + b + c + d-1,d + c-1,d-1,d + c + b-1]

private def word (corner : Bool) (a b c d r v : ℕ) : List ℕ :=
  let P := bank corner a b c d r v
  let T := terminal corner a b c d
  P 0 ++ T 0 :: P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3]

/- A power-of-two mask is ONE physical U occurrence, even when values coincide. -/
private theorem single_bit (len e : ℕ) (he : e<len) :
    (chamberLabels len 0 (2 ^ e)).Perm [e] := by
  apply (List.perm_ext_iff_of_nodup (chamberLabels_nodup _ _ _) (by simp)).mpr
  intro i
  simp only [chamberLabels_mem,List.mem_singleton]
  constructor
  · rintro ⟨j,hj,hbit,hji⟩
    have hje : e=j := of_decide_eq_true (by simpa only [Nat.testBit_two_pow] using hbit)
    omega
  · intro h
    subst i
    exact ⟨e,he,by simp [Nat.testBit_two_pow],by omega⟩

private theorem bank_inventory (corner : Bool) (a b c d r v : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (hda : d<a)
    (hr : 1 ≤ r) (hrn : r ≤ 2 ^ (a-d)) :
    (word corner a b c d r v).Perm (List.range (a + b + c + d)) := by
  let e := a-d
  let off := d + c + b
  let U := chamberLabels (d-1) 0
  let X := chamberLabels e off
  let hi := List.range' (off + e) (a-1-e)
  have hu := (chamberLabels_split (d-1) 0 (2 ^ (d-1)-1) v
    (by intro i hi _; simp [Nat.testBit_two_pow_sub_one,hi])).trans
    (List.Perm.of_eq (chamberLabels_full _ _))
  have hx := low_split e off r hr hrn
  have hxfull : (hi ++ X (2 ^ e-r) ++ X (r-1)).Perm (List.range' off (a-1)) := by
    have hh := hx.append_left hi
    have he : e + (a-1-e)=a-1 := by dsimp [e]; omega
    have hjoin : List.range' off e ++ hi=List.range' off (a-1) := by
      dsimp [hi]
      rw [List.range'_append_1,he]
    simpa only [List.append_assoc] using hh.trans
      ((List.perm_append_comm).trans (List.Perm.of_eq hjoin))
  have merge (o len : ℕ) (hlen : 1 ≤ len) :
      List.range' o (len-1) ++ [o + len-1]=List.range' o len := by
    simpa only [show o + (len-1)=o + len-1 by omega,show len-1 + 1=len by omega] using
      (List.range'_1_concat (s:=o) (n:=len-1)).symm
  have hall :
      (List.range' 0 (d-1) ++ [d-1]) ++ 
      (List.range' d (c-1) ++ [d + c-1]) ++ 
      (List.range' (d + c) (b-1) ++ [d + c + b-1]) ++ 
      (List.range' off (a-1) ++ [a + b + c + d-1])=List.range (a + b + c + d) := by
    have h0 := merge 0 d (by omega)
    simp only [Nat.zero_add] at h0
    rw [h0,merge d c (by omega),merge (d + c) b (by omega)]
    have ht : a + b + c + d-1=off + a-1 := by dsimp [off]; omega
    rw [ht,merge off a (by omega)]
    dsimp [off]
    have hdc : List.range' 0 d ++ List.range' d c = List.range' 0 (d+c) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=d) (n:=c))
    have hdcb : List.range' 0 (d+c) ++ List.range' (d+c) b = List.range' 0 (d+c+b) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=d+c) (n:=b))
    have hdcba : List.range' 0 (d+c+b) ++ List.range' (d+c+b) a = List.range' 0 (d+c+b+a) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=d+c+b) (n:=a))
    rw [hdc,hdcb,hdcba]
    simp only [Nat.zero_add,←List.range_eq_range']
    congr 1
    omega
  have hw : word corner a b c d r v =
      bank corner a b c d r v 0 ++ [terminal corner a b c d 0] ++ 
      bank corner a b c d r v 1 ++ [terminal corner a b c d 1] ++ 
      bank corner a b c d r v 2 ++ [terminal corner a b c d 2] ++ 
      bank corner a b c d r v 3 ++ [terminal corner a b c d 3] := by
    simp only [word,List.append_assoc,List.singleton_append]
  apply Multiset.coe_eq_coe.mp
  calc
    (word corner a b c d r v : Multiset ℕ) =
        (↑(U ((2 ^ (d-1)-1) ^^^ v) ++ U v) : Multiset ℕ) + 
        ↑(List.range' d (c-1)) + ↑(List.range' (d + c) (b-1)) + 
        ↑(hi ++ X (2 ^ e-r) ++ X (r-1)) + 
        {d-1} + {d + c-1} + {d + c + b-1} + {a + b + c + d-1} := by
      rw [hw]
      cases corner <;> dsimp [bank,terminal,U,X,hi,e,off]
      all_goals simp only [←Multiset.coe_add,Multiset.coe_singleton]
      all_goals ac_rfl
    _ = ↑(List.range' 0 (d-1)) + ↑(List.range' d (c-1)) + 
        ↑(List.range' (d + c) (b-1)) + ↑(List.range' off (a-1)) + 
        {d-1} + {d + c-1} + {d + c + b-1} + {a + b + c + d-1} := by
      rw [Multiset.coe_eq_coe.mpr hu,Multiset.coe_eq_coe.mpr hxfull]
    _ = (List.range (a + b + c + d) : Multiset ℕ) := by
      rw [←hall]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl

private theorem bank_good (corner : Bool) (a b c d r v : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (hda : d<a)
    (j : Fin 4) (i : ℕ) (hi : i∈bank corner a b c d r v j) :
    i<size a b c d ∧ i∉negatives a b c d := by
  have masked (len off m : ℕ) (hm : i∈chamberLabels len off m) : off ≤ i ∧ i<off + len := by
    obtain ⟨e,he,_,hei⟩ := (chamberLabels_mem _ _ _ _).mp hm
    omega
  cases corner <;> fin_cases j
  all_goals dsimp [bank] at hi
  all_goals try simp only [List.mem_append] at hi
  all_goals repeat' first
    | (have h := masked _ _ _ hi
       constructor
       · dsimp [size]; omega
       · simp only [negatives,size,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false]; omega)
    | (rw [List.mem_range'] at hi
       constructor
       · dsimp [size]; omega
       · simp only [negatives,size,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false]; omega)
    | rcases hi with hi|hi

/- Same physical banks, evaluated in each ACTUAL centered source row. -/
private theorem bank_masses (corner : Bool) (a b c d r v : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (hda : d<a)
    (hr : 1 ≤ r) (hrn : r ≤ 2 ^ (a-d)) (hv : v<2 ^ (d-1))
    (hbit : corner=true → ∃ e, e<d-1 ∧ v=2 ^ e) :
    ∀ side : Bool,
    let F := if side then newBase a b c d else base a b c d
    let f := if side then newValue a b c d else oldValue a b c d
    let C := fun j : Fin 4 => (((2 ^ (chainLength a b c d j-1)-1:ℕ):ℤ)) * F j
    let P := bank corner a b c d r v
    let p := ((2 ^ (a-d)-r:ℕ):ℤ) * F 3
    let q := ((r-1:ℕ):ℤ) * F 3
    let uv := (v:ℤ) * F 0
    ((P 0).map f).sum=C 3-((2 ^ (a-d):ℕ):ℤ) * F 3 + F 3 ∧ 
    ((P 1).map f).sum=(if corner then C 0-uv + p else C 1 + p + uv) ∧ 
    ((P 2).map f).sum=(if corner then C 1 + uv else C 0-uv) ∧ 
    ((P 3).map f).sum=C 2 + q := by
  intro side
  dsimp only
  let F := if side then newBase a b c d else base a b c d
  let f := if side then newValue a b c d else oldValue a b c d
  let C := fun j : Fin 4 => (((2 ^ (chainLength a b c d j-1)-1:ℕ):ℤ)) * F j
  let e := a-d
  let off := d + c + b
  have tab := chain_values a b c d ha hb hc hd
  have hseries (j : Fin 4) : ∀ i<chainLength a b c d j-1,
      f (chainStart b c d j + i)=2 ^ i * F j := by
    intro i hi
    cases side
    · exact (tab.2.1 j i (by omega)).trans (if_pos (by omega))
    · exact (tab.2.2.1 j i (by omega)).trans (if_pos (by omega))
  have full (j : Fin 4) :
      ((List.range' (chainStart b c d j) (chainLength a b c d j-1)).map f).sum=C j := by
    rw [←chamberLabels_full]
    apply chamberLabels_sum
    · exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    · exact hseries j
  have su : ((chamberLabels (d-1) 0 v).map f).sum=(v:ℤ) * F 0 := by
    by_cases hcorner : corner=true
    · obtain ⟨e,he,hev⟩ := hbit hcorner
      have hsingle := ((single_bit (d-1) e he).map f).sum_eq
      simp only [List.map_singleton,List.sum_singleton] at hsingle
      rw [hev,hsingle]
      have hs := hseries 0 e (by simpa [chainLength] using he)
      simpa [chainStart] using hs
    · exact chamberLabels_sum (d-1) 0 v hv f (F 0)
        (by simpa [chainLength,chainStart] using hseries 0)
  have hpCap : 2 ^ e-r<2 ^ e := by dsimp [e]; omega
  have hqCap : r-1<2 ^ e := by dsimp [e]; omega
  have hxseries : ∀ i<e, f (off + i)=2 ^ i * F 3 := by
    intro i hi
    exact hseries 3 i (by dsimp [chainLength,e] at * ; omega)
  have sp := chamberLabels_sum e off (2 ^ e-r) hpCap f (F 3) hxseries
  have sq := chamberLabels_sum e off (r-1) hqCap f (F 3) hxseries
  have hu := ((chamberLabels_split (d-1) 0 (2 ^ (d-1)-1) v
    (by intro i hi _; simp [Nat.testBit_two_pow_sub_one,hi])).map f).sum_eq
  rw [chamberLabels_full] at hu
  simp only [List.map_append,List.sum_append] at hu
  have f0 := full 0
  change ((List.range' 0 (d-1)).map f).sum = C 0 at f0
  rw [su,f0] at hu
  have uc : ((chamberLabels (d-1) 0 ((2 ^ (d-1)-1) ^^^ v)).map f).sum=C 0-(v:ℤ) * F 0 := by omega
  have hx := ((low_split e off r hr hrn).map f).sum_eq
  simp only [List.map_append,List.sum_append] at hx
  rw [sp,sq] at hx
  have hlen : e + (a-1-e)=a-1 := by dsimp [e]; omega
  have hxjoin : List.range' off e ++ List.range' (off + e) (a-1-e)=List.range' off (a-1) := by
    rw [List.range'_append_1,hlen]
  have hsum := congrArg (fun l : List ℕ => (l.map f).sum) hxjoin
  simp only [List.map_append,List.sum_append] at hsum
  have hX := full 3
  change ((List.range' off (a-1)).map f).sum=C 3 at hX
  rw [hX,←hx] at hsum
  have cp : ((2 ^ e-r:ℕ):ℤ)=((2 ^ e:ℕ):ℤ)-(r:ℤ) := Nat.cast_sub hrn
  have cq : ((r-1:ℕ):ℤ)=(r:ℤ)-1 := by rw [Nat.cast_sub hr]; norm_num
  have high : ((List.range' (off + e) (a-1-e)).map f).sum=C 3-((2 ^ e:ℕ):ℤ) * F 3 + F 3 := by
    rw [cp,cq] at hsum
    nlinarith only [hsum]
  have hV := full 1
  have hW := full 2
  change ((List.range' d (c-1)).map f).sum=C 1 at hV
  change ((List.range' (d + c) (b-1)).map f).sum=C 2 at hW
  cases corner <;> dsimp [bank]
  all_goals simp only [List.map_append,List.sum_append]
  all_goals refine ⟨high,?_,?_,?_⟩
  all_goals first | rw [uc,sp] | rw [hV,sp,su] | rw [hV,su] | exact uc | rw [hW,sq]

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Descending
