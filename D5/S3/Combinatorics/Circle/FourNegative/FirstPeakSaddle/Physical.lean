/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Physical
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:private-consumed-full-saddle-implementation)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: One physical permutation and one literal fresh-label cut control both complete source rows. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.Source
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

/-! SOURCE_ONLY_UNCOMPILED. Generic physical construction for every strict saddle.
All new declarations are private and occur on the path to actualSource_of_nativeChoice.
No arithmetic selection, public endpoint, build or acceptance is supplied by this file. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators

open private gate JointChoice JointChoice.s JointChoice.r JointChoice.h JointChoice.v
  JointChoice.bounds JointChoice.submask JointChoice.good
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.Structure
open private source_parity source_centered_bounds source_recurrences
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.Source
open private size sourceMod base newBase charge chainLength chainStart nextBase nextNewBase
  oldValue newValue negatives chain_values source_signs source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private four_perm four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private half_power from D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint

/- Native original occurrence sets and exact geometric masses. -/
open MaxPlusTwo.Chambers
private def bits (len off m : ℕ) : Finset ℕ := (chamberLabels len off m).toFinset

private theorem bits_mem (len off m i : ℕ) :
    i∈bits len off m ↔ ∃ e<len, m.testBit e=true ∧ off+e=i := by
  simp only [bits,List.mem_toFinset,chamberLabels_mem]

private theorem bits_region (len off m i : ℕ) (hi : i∈bits len off m) :
    off≤i ∧ i<off+len := by
  obtain ⟨e,he,_,hh⟩ := (bits_mem len off m i).mp hi
  omega

private theorem bits_full (len off : ℕ) :
    bits len off (2^len-1)=Finset.Ico off (off+len) := by
  ext i
  rw [bits_mem]
  constructor
  · rintro ⟨e,he,_,hh⟩
    simp only [Finset.mem_Ico]
    omega
  · intro hi
    simp only [Finset.mem_Ico] at hi
    refine ⟨i-off,by omega,?_,by omega⟩
    simp [Nat.testBit_two_pow_sub_one,show i-off<len by omega]

private theorem bits_subset_full (len off m : ℕ) :
    bits len off m ⊆ bits len off (2^len-1) := by
  intro i hi
  rw [bits_full]
  exact Finset.mem_Ico.mpr (bits_region len off m i hi)

private theorem bits_submask (len off m u : ℕ)
    (hs : ∀ e<len, u.testBit e=true → m.testBit e=true) :
    bits len off u ⊆ bits len off m := by
  intro i hi
  obtain ⟨e,he,hb,hh⟩ := (bits_mem len off u i).mp hi
  exact (bits_mem len off m i).mpr ⟨e,he,hs e he hb,hh⟩

private theorem bits_sum (len off m : ℕ) (hm : m<2^len)
    (f : ℕ→ℤ) (F : ℤ) (hf : ∀ e<len, f (off+e)=(2:ℤ)^e*F) :
    (∑ i∈bits len off m, f i)=(m:ℤ)*F := by
  have hp : (bits len off m).toList.Perm (chamberLabels len off m) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
      (chamberLabels_nodup len off m)).mpr
    intro i
    simp only [Finset.mem_toList, bits, List.mem_toFinset]
  have hs : ((bits len off m).toList.map f).sum = ∑ i∈bits len off m, f i := by
    change (((bits len off m).toList : Multiset ℕ).map f).sum = _
    rw [Finset.coe_toList]
    rfl
  rw [←hs, (hp.map f).sum_eq]
  exact chamberLabels_sum len off m hm f F hf

private theorem bits_difference_sum (len off m u : ℕ) (hm : m<2^len) (hu : u<2^len)
    (hs : bits len off u ⊆ bits len off m)
    (f : ℕ→ℤ) (F : ℤ) (hf : ∀ e<len, f (off+e)=(2:ℤ)^e*F) :
    (∑ i∈bits len off m \ bits len off u, f i)=((m:ℤ)-u)*F := by
  have hh := Finset.sum_sdiff (f:=f) hs
  rw [bits_sum len off m hm f F hf,bits_sum len off u hu f F hf] at hh
  linarith

private def selected (a b c d : ℕ) (ch : JointChoice a b c d) : Fin 3 → Finset ℕ :=
  let U := bits (d-1) 0 (2^(d-1)-1)
  let Uv := bits (d-1) 0 ch.v
  let Wh := bits (b-1) (d+c) ch.h
  let X := bits (a-1) (d+c+b) (2^(a-1)-1)
  let Xm := bits (a-1) (d+c+b) (ch.s-1)
  let Xu := bits (a-1) (d+c+b) (ch.r-1)
  let V := bits (c-1) d (2^(c-1)-1)
  ![(U \ Uv) ∪ Wh ∪ (X \ Xm), Xm \ Xu, Uv ∪ V ∪ Xu]

private theorem selected_good (a b c d : ℕ) (hd : 3≤d) (hc : 2≤c) (hdb : d<b) (hba : b<a)
    (ch : JointChoice a b c d) :
    (∀ j : Fin 3, ∀ i∈selected a b c d ch j,
      i<a+b+c+d ∧ i≠a+b+c+d-1 ∧ i≠d+c-1 ∧ i≠d-1 ∧ i≠d+c+b-1) ∧
    (∀ j l : Fin 3, j≠l → Disjoint (selected a b c d ch j) (selected a b c d ch l)) := by
  have hsub := bits_submask (a-1) (d+c+b) (ch.s-1) (ch.r-1) ch.submask
  have g0 : ∀ i∈selected a b c d ch 0,
      i<a+b+c+d ∧ i≠a+b+c+d-1 ∧ i≠d+c-1 ∧ i≠d-1 ∧ i≠d+c+b-1 := by
    intro i hi
    simp only [selected,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Finset.mem_union,Finset.mem_sdiff] at hi
    rcases hi with (hi|hi)|hi
    · have hb := bits_region (d-1) (0) (2^(d-1)-1) i hi.1
      omega
    · have hb := bits_region (b-1) (d+c) (ch.h) i hi
      omega
    · have hb := bits_region (a-1) (d+c+b) (2^(a-1)-1) i hi.1
      omega
  have g1 : ∀ i∈selected a b c d ch 1,
      i<a+b+c+d ∧ i≠a+b+c+d-1 ∧ i≠d+c-1 ∧ i≠d-1 ∧ i≠d+c+b-1 := by
    intro i hi
    simp only [selected,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Finset.mem_union,Finset.mem_sdiff] at hi
    have hb := bits_region (a-1) (d+c+b) (ch.s-1) i hi.1
    omega
  have g2 : ∀ i∈selected a b c d ch 2,
      i<a+b+c+d ∧ i≠a+b+c+d-1 ∧ i≠d+c-1 ∧ i≠d-1 ∧ i≠d+c+b-1 := by
    intro i hi
    simp only [selected,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Finset.mem_union,Finset.mem_sdiff] at hi
    rcases hi with (hi|hi)|hi
    · have hb := bits_region (d-1) (0) (ch.v) i hi
      omega
    · have hb := bits_region (c-1) d (2^(c-1)-1) i hi
      omega
    · have hb := bits_region (a-1) (d+c+b) (ch.r-1) i hi
      omega
  have d01 : Disjoint (selected a b c d ch 0) (selected a b c d ch 1) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [selected,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Finset.mem_union,Finset.mem_sdiff] at hi hj
    rcases hi with (hi|hi)|hi
    · have hb := bits_region (d-1) (0) (2^(d-1)-1) i hi.1
      have hc := bits_region (a-1) (d+c+b) (ch.s-1) i hj.1
      omega
    · have hb := bits_region (b-1) (d+c) (ch.h) i hi
      have hc := bits_region (a-1) (d+c+b) (ch.s-1) i hj.1
      omega
    · exact hi.2 hj.1
  have d02 : Disjoint (selected a b c d ch 0) (selected a b c d ch 2) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [selected,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Finset.mem_union,Finset.mem_sdiff] at hi hj
    rcases hi with (hi|hi)|hi
    · rcases hj with (hj|hj)|hj
      · exact hi.2 hj
      · have hb := bits_region (d-1) (0) (2^(d-1)-1) i hi.1
        have hc := bits_region (c-1) d (2^(c-1)-1) i hj
        omega
      · have hb := bits_region (d-1) (0) (2^(d-1)-1) i hi.1
        have hc := bits_region (a-1) (d+c+b) (ch.r-1) i hj
        omega
    · rcases hj with (hj|hj)|hj
      · have hb := bits_region (b-1) (d+c) (ch.h) i hi
        have hc := bits_region (d-1) (0) (ch.v) i hj
        omega
      · have hb := bits_region (b-1) (d+c) (ch.h) i hi
        have hc := bits_region (c-1) d (2^(c-1)-1) i hj
        omega
      · have hb := bits_region (b-1) (d+c) (ch.h) i hi
        have hc := bits_region (a-1) (d+c+b) (ch.r-1) i hj
        omega
    · rcases hj with (hj|hj)|hj
      · have hb := bits_region (a-1) (d+c+b) (2^(a-1)-1) i hi.1
        have hc := bits_region (d-1) (0) (ch.v) i hj
        omega
      · have hb := bits_region (a-1) (d+c+b) (2^(a-1)-1) i hi.1
        have hc := bits_region (c-1) d (2^(c-1)-1) i hj
        omega
      · exact hi.2 (hsub hj)
  have d12 : Disjoint (selected a b c d ch 1) (selected a b c d ch 2) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [selected,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Finset.mem_union,Finset.mem_sdiff] at hi hj
    rcases hj with (hj|hj)|hj
    · have hb := bits_region (a-1) (d+c+b) (ch.s-1) i hi.1
      have hc := bits_region (d-1) (0) (ch.v) i hj
      omega
    · have hb := bits_region (a-1) (d+c+b) (ch.s-1) i hi.1
      have hc := bits_region (c-1) d (2^(c-1)-1) i hj
      omega
    · exact hi.2 hj
  constructor
  · intro j
    fin_cases j
    all_goals first | exact g0 | exact g1 | exact g2
  · intro j l hne
    fin_cases j <;> fin_cases l
    all_goals first | exact (hne rfl).elim | exact d01 | exact d02 | exact d12 |
      exact d01.symm | exact d02.symm | exact d12.symm

private theorem remainder_eq (a b c d : ℕ) (hd : 3≤d) (hc : 2≤c) (hdb : d<b) (hba : b<a)
    (ch : JointChoice a b c d) :
    Finset.range (a+b+c+d) \ (selected a b c d ch 0 ∪ selected a b c d ch 1 ∪
      selected a b c d ch 2 ∪ {a+b+c+d-1,d+c-1,d-1,d+c+b-1}) =
    bits (b-1) (d+c) (2^(b-1)-1) \ bits (b-1) (d+c) ch.h := by
  ext i
  have hu := bits_region (d-1) 0 ch.v i
  have hw := bits_region (b-1) (d+c) ch.h i
  have hm := bits_region (a-1) (d+c+b) (ch.s-1) i
  have hx := bits_submask (a-1) (d+c+b) (ch.s-1) (ch.r-1) ch.submask
  have hx' : i∈bits (a-1) (d+c+b) (ch.r-1) → i∈bits (a-1) (d+c+b) (ch.s-1) := hx
  simp only [selected,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,
    Matrix.vecTail,Function.comp_apply,bits_full,
    Finset.mem_range,Finset.mem_union,Finset.mem_sdiff,Finset.mem_insert,
    Finset.mem_singleton,Finset.mem_Ico]
  omega

private theorem sumlist (P : Finset ℕ) (f : ℕ→ℤ) :
    (P.toList.map f).sum=∑ i∈P,f i := by
  change ((P.toList : Multiset ℕ).map f).sum=_
  simp

private theorem selected_mass (a b c d : ℕ) (hd : 3≤d) (hc : 2≤c) (hdb : d<b) (hba : b<a)
    (ch : JointChoice a b c d) (f : ℕ→ℤ) (A B L M : ℤ)
    (hU : ∀ e<d-1, f (0+e)=(2:ℤ)^e*A)
    (hV : ∀ e<c-1, f (d+e)=(2:ℤ)^e*B)
    (hW : ∀ e<b-1, f (d+c+e)=(2:ℤ)^e*L)
    (hX : ∀ e<a-1, f (d+c+b+e)=(2:ℤ)^e*M) :
    ((selected a b c d ch 0).toList.map f).sum =
      ((2:ℤ)^(d-1)-1-ch.v)*A+ch.h*L+((2:ℤ)^(a-1)-ch.s)*M ∧
    ((selected a b c d ch 1).toList.map f).sum = ((ch.s:ℤ)-ch.r)*M ∧
    ((selected a b c d ch 2).toList.map f).sum = ch.v*A+((2:ℤ)^(c-1)-1)*B+((ch.r:ℤ)-1)*M := by
  have hb := ch.bounds
  have hs : 1≤ch.s := by omega
  have hm : ch.s-1<2^(a-1) := by omega
  have hu : ch.r-1<2^(a-1) := by omega
  have hp (n : ℕ) : 2^n-1<2^n := by have := Nat.one_le_two_pow (n:=n); omega
  have hsub := bits_submask (a-1) (d+c+b) (ch.s-1) (ch.r-1) ch.submask
  have mU := bits_difference_sum (d-1) 0 (2^(d-1)-1) ch.v (hp _) hb.2.2.2.1
    (bits_subset_full _ _ _) f A hU
  have mW := bits_sum (b-1) (d+c) ch.h hb.2.2.2.2 f L hW
  have mX := bits_difference_sum (a-1) (d+c+b) (2^(a-1)-1) (ch.s-1)
    (hp _) hm (bits_subset_full _ _ _) f M hX
  have mQ := bits_difference_sum (a-1) (d+c+b) (ch.s-1) (ch.r-1) hm hu hsub f M hX
  have mV := bits_sum (c-1) d (2^(c-1)-1) (hp _) f B hV
  have mv := bits_sum (d-1) 0 ch.v hb.2.2.2.1 f A hU
  have mu := bits_sum (a-1) (d+c+b) (ch.r-1) hu f M hX
  have dis (l o m l' o' m' : ℕ) (he : o+l≤o' ∨ o'+l'≤o) :
      Disjoint (bits l o m) (bits l' o' m') := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' := bits_region l o m i hi
    have hj' := bits_region l' o' m' i hj
    omega
  have duw : Disjoint (bits (d-1) 0 (2^(d-1)-1) \ bits (d-1) 0 ch.v)
      (bits (b-1) (d+c) ch.h) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp (dis _ _ _ _ _ _ (Or.inl (by omega)))
      (Finset.mem_sdiff.mp hi).1 hj
  have dux : Disjoint (bits (d-1) 0 (2^(d-1)-1) \ bits (d-1) 0 ch.v)
      (bits (a-1) (d+c+b) (2^(a-1)-1) \ bits (a-1) (d+c+b) (ch.s-1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp (dis _ _ _ _ _ _ (Or.inl (by omega)))
      (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1
  have dwx : Disjoint (bits (b-1) (d+c) ch.h)
      (bits (a-1) (d+c+b) (2^(a-1)-1) \ bits (a-1) (d+c+b) (ch.s-1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp (dis _ _ _ _ _ _ (Or.inl (by omega))) hi
      (Finset.mem_sdiff.mp hj).1
  have duv := dis (d-1) 0 ch.v (c-1) d (2^(c-1)-1) (Or.inl (by omega))
  have dux' := dis (d-1) 0 ch.v (a-1) (d+c+b) (ch.r-1) (Or.inl (by omega))
  have dvx := dis (c-1) d (2^(c-1)-1) (a-1) (d+c+b) (ch.r-1) (Or.inl (by omega))
  simp only [sumlist,selected,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨dux,dwx⟩),
    Finset.sum_union duw,Finset.sum_union (Finset.disjoint_union_left.mpr ⟨dux',dvx⟩),
    Finset.sum_union duv,mU,mW,mX,mQ,mV,mv,mu]
  have huN : 1≤2^(d-1) := Nat.one_le_two_pow
  have hxN : 1≤2^(a-1) := Nat.one_le_two_pow
  rw [Nat.cast_sub huN,Nat.cast_sub hxN,Nat.cast_sub hs,Nat.cast_sub hb.1]
  push_cast
  constructor
  · ring
  constructor <;> ring


private theorem twice_terminal (N q : ℤ) (hN : N%2=1) (hq : q%2=1) :
    2*(-(N-q)/2)=q-N := by omega

set_option maxHeartbeats 2400000 in
/-- The complete physical reconstruction, consuming one native arithmetic choice.
Consumed by the sole public eight-binder theorem after Native proves existence. -/
private theorem actualSource_of_nativeChoice
    (a b c d : ℕ) (hc : 2≤c) (hcd : c<d) (hdb : d<b) (hba : b<a)
    (ch : JointChoice a b c d) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ cut : ℕ, cut≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma cut) := by
  classical
  let k := a+b+c+d
  let alpha := 1+2^a+2^(a+b)+2^(a+b+c)
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let t : ℤ := 2^d
  let z : ℤ := 2^c
  let D := y*(z+1)+1
  let A := x*D+1
  let B := x*t*(y+1)+t+1
  let L := x*z*t+z*t+z+1
  let M := t*y*z+D
  let Bn := 2*B-1
  let Ln := 2*L-z-1
  let Mn := 2*M-D
  let N := sourceMod a b c d
  let f := oldValue a b c d
  let g := newValue a b c d
  let s : ℤ := ch.s
  let r : ℤ := ch.r
  let h : ℤ := ch.h
  let v : ℤ := ch.v
  let E1 := (t-2*v)*A-2*s*M+2*h*L
  let E2 := B+L-2*v*A-2*r*M+2*h*L
  let E3 := 2*(h+1)*L-2*M
  let F1 := 2*((t-1-2*v)*A-s*Mn+h*Ln)
  let F2 := Bn+Ln-4*v*A-2*r*Mn+2*h*Ln
  let F3 := 2*((h+1)*Ln-Mn)
  have hbase : base a b c d = ![A,B,L,M] := by
    funext j
    fin_cases j <;> dsimp [base,A,B,L,M,D,x,y,z,t] <;> norm_num <;> ring
  have hnewbase : newBase a b c d = ![2*A,Bn,Ln,Mn] := by
    funext j
    fin_cases j <;> dsimp [newBase,charge,Bn,Ln,Mn]
    all_goals rw [hbase] <;> dsimp [D,y,z] <;> norm_num <;> ring
  have halpha : (alpha:ℤ)=A := by
    dsimp [alpha,A,D,x,y,z]
    push_cast
    simp only [pow_add]
    norm_num
    ring
  have hmod : modulus k=N := by
    dsimp [k,N,sourceMod,modulus]
    simp only [pow_add]
    ring
  have hmod' : modulus (k+1)=2*N+1 := by
    dsimp [k,N,sourceMod,modulus]
    simp only [pow_add, pow_succ]
    ring
  have hxhalf : x=2*(2:ℤ)^(a-1) := half_power a (by omega)
  have hthalf : t=2*(2:ℤ)^(d-1) := half_power d (by omega)
  have hzhalf : z=2*(2:ℤ)^(c-1) := half_power c (by omega)
  have parity := source_parity a b c d (by omega) (by omega) hc (by omega)
  have bounded := source_centered_bounds a b c d (by omega) (by omega) hc (by omega)
  have recurrence := source_recurrences a b c d
  have hNodd : N%2=1 := parity.1
  have hAodd : A%2=1 := by simpa [hbase] using parity.2.1 0
  have hBodd : B%2=1 := by simpa [hbase] using parity.2.1 1
  have hLodd : L%2=1 := by simpa [hbase] using parity.2.1 2
  have hQodd : (2*N+1)%2=1 := by omega
  have hBnodd : Bn%2=1 := by simpa [nextNewBase,hnewbase] using parity.2.2 0
  have hLnodd : Ln%2=1 := by simpa [nextNewBase,hnewbase] using parity.2.2 1
  have tab := chain_values a b c d (by omega) (by omega) hc (by omega)
  have positives (j : Fin 4) (e : ℕ) (he : e+1<chainLength a b c d j) :
      f (chainStart b c d j+e)=(2:ℤ)^e*base a b c d j ∧
      g (chainStart b c d j+e)=(2:ℤ)^e*newBase a b c d j := by
    exact ⟨by simpa only [if_pos he] using tab.2.1 j e (by omega),
      by simpa only [if_pos he] using tab.2.2.1 j e (by omega)⟩
  have mf := selected_mass a b c d (by omega) hc hdb hba ch f A B L M
    (fun e he => by simpa [chainStart,hbase] using (positives 0 e (by dsimp [chainLength]; omega)).1)
    (fun e he => by simpa [chainStart,hbase] using (positives 1 e (by dsimp [chainLength]; omega)).1)
    (fun e he => by simpa [chainStart,hbase] using (positives 2 e (by dsimp [chainLength]; omega)).1)
    (fun e he => by simpa [chainStart,hbase] using (positives 3 e (by dsimp [chainLength]; omega)).1)
  have mg := selected_mass a b c d (by omega) hc hdb hba ch g (2*A) Bn Ln Mn
    (fun e he => by simpa [chainStart,hnewbase] using (positives 0 e (by dsimp [chainLength]; omega)).2)
    (fun e he => by simpa [chainStart,hnewbase] using (positives 1 e (by dsimp [chainLength]; omega)).2)
    (fun e he => by simpa [chainStart,hnewbase] using (positives 2 e (by dsimp [chainLength]; omega)).2)
    (fun e he => by simpa [chainStart,hnewbase] using (positives 3 e (by dsimp [chainLength]; omega)).2)
  let P := selected a b c d ch 0
  let Q := selected a b c d ch 1
  let R := selected a b c d ch 2
  let nx := k-1
  let nv := d+c-1
  let nu := d-1
  let nw := d+c+b-1
  let G := Finset.range k \ (P ∪ Q ∪ R ∪ {nx,nv,nu,nw})
  let first := P.toList ++ [nx]
  let rest := Q.toList ++ nv :: R.toList ++ nu :: G.toList ++ [nw]
  let word := first ++ rest
  have good := selected_good a b c d (by omega) hc hdb hba ch
  have hp := four_perm k nx nv nu nw P Q R (good.1 0) (good.1 1) (good.1 2)
    (good.2 0 1 (by decide)) (good.2 0 2 (by decide)) (good.2 1 2 (by decide))
    (by simp [nx,nv,nu,nw,k]; omega)
    (by intro i hi
        simp only [List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl <;> dsimp [nx,nv,nu,nw,k] <;> omega)
  have hp : word.Perm (List.range k) := by
    simpa only [word,first,rest,G,List.append_assoc,List.singleton_append,
      List.cons_append,List.nil_append] using hp
  have allpos (i : ℕ) (hi : i<k) (hn : i≠nx ∧ i≠nv ∧ i≠nu ∧ i≠nw) :
      0≤f i ∧ 0≤g i := by
    have hh := source_signs a b c d (by omega) (by omega) hc (by omega) i hi
    have hnot : i∉negatives a b c d := by
      intro he
      simp only [negatives,size,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at he
      dsimp [nx,nv,nu,nw,k] at hn
      rcases he with he|he|he|he <;> omega
    rw [if_neg hnot] at hh
    exact ⟨hh.1.le,hh.2.le⟩
  have pos (j : Fin 3) (i : ℕ) (hi : i∈(selected a b c d ch j).toList) :
      0≤f i ∧ 0≤g i := by
    have hh := good.1 j i (Finset.mem_toList.mp hi)
    exact allpos i hh.1 hh.2
  have Gform : G=bits (b-1) (d+c) (2^(b-1)-1) \ bits (b-1) (d+c) ch.h :=
    remainder_eq a b c d (by omega) hc hdb hba ch
  have posG (i : ℕ) (hi : i∈G.toList) : 0≤f i ∧ 0≤g i := by
    have hi' := Finset.mem_toList.mp hi
    rw [Gform] at hi'
    have hh := bits_region (b-1) (d+c) (2^(b-1)-1) i (Finset.mem_sdiff.mp hi').1
    apply allpos i
    · dsimp [k]; omega
    · dsimp [nx,nv,nu,nw,k]; omega
  have totals := source_totals a b c d (by omega) (by omega) hc (by omega)
  have hfzero : (word.map f).sum=0 := (hp.map f).sum_eq.trans totals.1
  have hear : g k=A := by simpa [k,size,hbase] using tab.2.2.2
  have hgzero : A+(word.map g).sum=0 := by
    have hh := (hp.map g).sum_eq.trans totals.2.1
    rw [hbase] at hh
    dsimp at hh
    omega
  have terminal (j : Fin 4) :
      f (chainStart b c d j+(chainLength a b c d j-1))=-(N-nextBase a b c d j)/2 ∧
      g (chainStart b c d j+(chainLength a b c d j-1))=-((2*N+1)-nextNewBase a b c d j)/2 := by
    have hl : 2≤chainLength a b c d j := by fin_cases j <;> dsimp [chainLength] <;> omega
    exact ⟨by simpa only [if_neg (by omega : ¬chainLength a b c d j-1+1<chainLength a b c d j)]
        using tab.2.1 j (chainLength a b c d j-1) (by omega),
      by simpa only [if_neg (by omega : ¬chainLength a b c d j-1+1<chainLength a b c d j)]
        using tab.2.2.1 j (chainLength a b c d j-1) (by omega)⟩
  have nt0 := terminal 3
  have nt1 := terminal 1
  have nt2 := terminal 0
  have nt3 := terminal 2
  simp only [chainStart,chainLength,nextBase,nextNewBase,hbase,hnewbase,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,
    Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,zero_add] at nt0 nt1 nt2 nt3
  have en0 : d+c+b+(a-1)=nx := by dsimp [nx,k]; omega
  have en1 : d+(c-1)=nv := by dsimp [nv]; omega
  have en3 : d+c+(b-1)=nw := by dsimp [nw]; omega
  rw [en0] at nt0
  rw [en1] at nt1
  rw [en3] at nt3
  have nf0 : 2*f nx=A-N := by rw [nt0.1]; exact twice_terminal N A hNodd hAodd
  have ng0 : 2*g nx=A-(2*N+1) := by rw [nt0.2]; exact twice_terminal _ A hQodd hAodd
  have nf1 : 2*f nv=L-N := by rw [nt1.1]; exact twice_terminal N L hNodd hLodd
  have ng1 : 2*g nv=Ln-(2*N+1) := by rw [nt1.2]; exact twice_terminal _ Ln hQodd hLnodd
  have nf2 : 2*f nu=B-N := by rw [nt2.1]; exact twice_terminal N B hNodd hBodd
  have ng2 : 2*g nu=Bn-(2*N+1) := by rw [nt2.2]; exact twice_terminal _ Bn hQodd hBnodd
  have relx : x*M=N+A := by
    simpa [chainLength,nextBase,hbase] using (recurrence 3).1
  have relt : t*A=N+B := by
    simpa [chainLength,nextBase,hbase] using (recurrence 0).1
  have relz : z*B=N+L := by
    simpa [chainLength,nextBase,hbase] using (recurrence 1).1
  have relxn : x*Mn=2*N+1+A := by
    simpa [chainLength,nextNewBase,hbase,hnewbase] using (recurrence 3).2
  have reltn : 2*t*A=2*N+1+Bn := by
    have hh := (recurrence 0).2
    simpa [chainLength,nextNewBase,hnewbase,mul_assoc,mul_left_comm,mul_comm] using hh
  have relzn : z*Bn=2*N+1+Ln := by
    simpa [chainLength,nextNewBase,hnewbase] using (recurrence 1).2
  have m0 : 2*(P.toList.map f).sum=(t-2-2*v)*A+2*h*L+(x-2*s)*M := by
    rw [hthalf,hxhalf]
    dsimp [P,s,h,v]
    nlinarith only [mf.1]
  have m1 : 2*(Q.toList.map f).sum=2*(s-r)*M := by dsimp [Q,s,r]; nlinarith only [mf.2.1]
  have m2 : 2*(R.toList.map f).sum=2*v*A+(z-2)*B+2*(r-1)*M := by
    have hzB := congrArg (fun u : ℤ => u*B) hzhalf
    dsimp [R,v,r]
    nlinarith only [mf.2.2,hzB]
  have j0 : 2*(P.toList.map g).sum=(t-2-2*v)*(2*A)+2*h*Ln+(x-2*s)*Mn := by
    rw [hthalf,hxhalf]
    dsimp [P,s,h,v]
    nlinarith only [mg.1]
  have j1 : 2*(Q.toList.map g).sum=2*(s-r)*Mn := by dsimp [Q,s,r]; nlinarith only [mg.2.1]
  have j2 : 2*(R.toList.map g).sum=4*v*A+(z-2)*Bn+2*(r-1)*Mn := by
    have hzB := congrArg (fun u : ℤ => u*Bn) hzhalf
    dsimp [R,v,r]
    nlinarith only [mg.2.2,hzB]
  have e1 : 2*((P.toList.map f).sum+f nx)=E1 := by
    dsimp [E1]; nlinarith only [m0,nf0,relx]
  have e2 : 2*((P.toList.map f).sum+f nx+(Q.toList.map f).sum+f nv)=E2 := by
    dsimp [E1] at e1
    dsimp [E2]; nlinarith only [e1,m1,nf1,relt]
  have e3 : 2*((P.toList.map f).sum+f nx+(Q.toList.map f).sum+f nv+
      (R.toList.map f).sum+f nu)=E3 := by
    dsimp [E2] at e2
    dsimp [E3]; nlinarith only [e2,m2,nf2,relz]
  have jQ : ((k::Q.toList).map g).sum=A+(Q.toList.map g).sum := by simp [hear]
  have f1 : 2*((P.toList.map g).sum+g nx)=F1 := by
    dsimp [F1]; nlinarith only [j0,ng0,relxn]
  have f2 : 2*((P.toList.map g).sum+g nx+((k::Q.toList).map g).sum+g nv)=F2 := by
    rw [jQ]
    dsimp [F1] at f1
    dsimp [F2]; nlinarith only [f1,j1,ng1,reltn]
  have f3 : 2*((P.toList.map g).sum+g nx+((k::Q.toList).map g).sum+g nv+
      (R.toList.map g).sum+g nu)=F3 := by
    dsimp [F2] at f2
    dsimp [F3]; nlinarith only [f2,j2,ng2,relzn]
  have hm0 := ch.good 0
  change 0≤E1 at hm0
  have hm1 := ch.good 1
  change 0≤A-1-E1 at hm1
  have hm2 := ch.good 2
  change 0≤F1 at hm2
  have hm3 := ch.good 3
  change 0≤A-1-F1 at hm3
  have hm4 := ch.good 4
  change 0≤E2 at hm4
  have hm5 := ch.good 5
  change 0≤L-1-E2 at hm5
  have hm6 := ch.good 6
  change 0≤F2 at hm6
  have hm7 := ch.good 7
  change 0≤Ln-1-F2 at hm7
  have hm8 := ch.good 8
  change 0≤E3 at hm8
  have hm9 := ch.good 9
  change 0≤B-1-E3 at hm9
  have hm10 := ch.good 10
  change 0≤F3 at hm10
  have hm11 := ch.good 11
  change 0≤Bn-1-F3 at hm11
  have hN0 : 0≤N := by
    have hb := tab.1 0
    change 1≤base a b c d 0 ∧ base a b c d 0<N at hb
    omega
  have hhalf : 2*(N/2)=N-1 := by omega
  have lastold : 0≤-f nw ∧ -f nw≤N/2 := by
    have hb := (bounded 3).1
    rw [hbase] at hb
    dsimp at hb
    rw [nt3.1]
    omega
  have lastnew : 0≤-g nw ∧ -g nw≤N := by
    have hb := (bounded 3).2
    rw [hnewbase] at hb
    dsimp at hb
    rw [nt3.2]
    omega
  have oldstrip : InStrip f (N/2) 0 word := by
    suffices hs : InStrip f (N/2) 0
        (P.toList ++ nx :: Q.toList ++ nv :: R.toList ++ nu :: G.toList ++ [nw]) by
      simpa only [word,first,rest,List.append_assoc,List.singleton_append,
        List.cons_append,List.nil_append] using hs
    apply four_strip f P.toList Q.toList R.toList G.toList nx nv nu nw (N/2) 0
      (fun i hi => (pos 0 i hi).1) (fun i hi => (pos 1 i hi).1)
      (fun i hi => (pos 2 i hi).1) (fun i hi => (posG i hi).1) (by omega)
    · constructor <;> linarith only [e1,nf0,hm0,hm1,hhalf]
    · constructor <;> linarith only [e2,nf1,hm4,hm5,hhalf]
    · constructor <;> linarith only [e3,nf2,hm8,hm9,hhalf]
    · exact lastold
    · simpa only [word,first,rest,List.append_assoc,List.singleton_append,
        List.cons_append,List.nil_append,zero_add] using hfzero
  have newstrip : InStrip g N 0 (first ++ k :: rest) := by
    have htzero : ((first ++ k :: rest).map g).sum=0 := by
      simpa [word,List.map_append,List.sum_append,hear,add_assoc,add_comm,add_left_comm] using hgzero
    have hs := four_strip g P.toList (k::Q.toList) R.toList G.toList nx nv nu nw N 0
      (fun i hi => (pos 0 i hi).2)
      (by intro i hi
          rcases List.mem_cons.mp hi with he|hi
          · subst i
            rw [hear]
            have hb := tab.1 0
            rw [hbase] at hb
            change 1≤A ∧ A<N at hb
            omega
          · exact (pos 1 i hi).2)
      (fun i hi => (pos 2 i hi).2) (fun i hi => (posG i hi).2) (by omega)
      (by constructor <;> linarith only [f1,ng0,hm2,hm3])
      (by constructor <;> linarith only [f2,ng1,hm6,hm7])
      (by constructor <;> linarith only [f3,ng2,hm10,hm11])
      lastnew (by simpa only [first,rest,List.append_assoc,List.singleton_append,
        List.cons_append,List.nil_append,zero_add] using htzero)
    simpa only [first,rest,List.append_assoc,List.singleton_append,
      List.cons_append,List.nil_append] using hs
  have hpnew : (first ++ k :: rest).Perm (List.range (k+1)) := by
    have hh : (first ++ k :: rest).Perm (word ++ [k]) := by
      simpa [word,List.append_assoc] using
        (List.perm_append_singleton k rest).symm.append_left first
    exact hh.trans (by simpa [List.range_succ] using hp.append_right [k])
  have fform : f=fun i => centered N ((2:ℤ)^i*A) := by
    funext i
    change centered N ((2:ℤ)^i*base a b c d 0)=_
    rw [hbase]
    rfl
  have gform : g=fun i => centered (2*N+1) ((2:ℤ)^i*(2*A)) := by
    funext i
    change centered (2*N+1) ((2:ℤ)^i*(2*base a b c d 0))=_
    rw [hbase]
    rfl
  refine ⟨word.map (label k (by dsimp [k]; omega)),first.length,?_,?_,?_⟩
  · have hl := hp.length_eq
    simp only [word,List.length_append,List.length_range] at hl
    dsimp [k] at hl ⊢
    omega
  · apply lift_order k alpha (by dsimp [k]; omega) word hp
    · simpa only [fform,hmod,halpha] using oldstrip
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k alpha (by dsimp [k]; omega)
  · have marked := marked_word k first.length (by dsimp [k]; omega) first rest rfl hp
    rw [marked]
    apply lift_order (k+1) (2*alpha) (by dsimp [k]; omega) (first ++ k :: rest) hpnew
    · have ha' : ((2*alpha:ℕ):ℤ)=2*A := by push_cast; rw [halpha]
      simpa only [gform,hmod',ha',show (2*N+1)/2=N by omega] using newstrip
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*alpha) (by dsimp [k]; omega)


end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle
