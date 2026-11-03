/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/ModeratePhysical
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: ThirdPeakEqualOuter ModeratePhysical for the complete original physical family. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModerateArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Source

/-! ThirdPeakEqualOuter: ModeratePhysical. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private A B L K SU SV SW Window
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Arithmetic
open private FirstTwoWindows
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModerateArithmetic
open private F G nextF nextG bases positive_rows terminal_rows stock_nonnegative
  four_windows_strip Joint realize_split
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Source
open private size sourceMod base chainLength chainStart oldValue newValue source_totals chain_values
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private full stock complement terminals stock_split canonical_inventory stock_good
  stock_mass complement_mass lowV highV highComplement high_split v_inventory high_mass
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks

set_option maxHeartbeats 1800000 in
private theorem moderate_realize (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (P : Fin 4 → List ℕ) (early : Bool) (E Ep R Rp : ℤ)
    (hp : (P 0++[a-1]++P 1++[a+c-1]++P 2++[a+c+b-1]++P 3++[a+b+c+a-1]).Perm
      (List.range (a+b+c+a)))
    (hpos : ∀ j : Fin 4, ∀ i ∈ P j, 0 ≤ oldValue a b c a i ∧ 0 ≤ newValue a b c a i)
    (h1 : ((P 0).map (oldValue a b c a)).sum+oldValue a b c a (a-1)=E)
    (h1n : ((P 0).map (newValue a b c a)).sum+newValue a b c a (a-1)=Ep)
    (h2 : E+((P 1).map (oldValue a b c a)).sum+oldValue a b c a (a+c-1)=R)
    (h2n : Ep+((P 1).map (newValue a b c a)).sum+newValue a b c a (a+c-1)=Rp)
    (h3 : R+((P 2).map (oldValue a b c a)).sum+oldValue a b c a (a+c+b-1)=
      K (2^a) (2^b) (2^c)-A (2^a) (2^b) (2^c))
    (h3n : Rp+((P 2).map (newValue a b c a)).sum+newValue a b c a (a+c+b-1)=
      SW (2^a) (2^b) (2^c)-2*A (2^a) (2^b) (2^c))
    (hfirst : FirstTwoWindows (2^a) (2^b) (2^c) E Ep R Rp)
    (hW : Window (K (2^a) (2^b) (2^c)-A (2^a) (2^b) (2^c)) (K (2^a) (2^b) (2^c)))
    (hWn : Window (SW (2^a) (2^b) (2^c)-2*A (2^a) (2^b) (2^c)+
      (if early then A (2^a) (2^b) (2^c) else 0)) (SW (2^a) (2^b) (2^c))) :
    Joint a b c := by
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let N := sourceMod a b c a
  let f := oldValue a b c a
  let g := newValue a b c a
  let k := a+b+c+a
  let l := P 0++[a-1]++P 1++[a+c-1]++P 2++[a+c+b-1]++P 3++[k-1]
  have nt (j : Fin 4) := terminal_rows a b c ha hb hc j
  have step (j : Fin 4) :
      2*f (terminals a b c a j)=nextF x y z j-N ∧
      2*g (terminals a b c a j)=nextG x y z j-(2*N+1) := ⟨(nt j).2.2.1,(nt j).2.2.2⟩
  have totals := source_totals a b c a ha hb hc ha
  have oldzero : (l.map f).sum=0 := (hp.map f).sum_eq.trans totals.1
  have newold : (l.map g).sum= -A x y z := by
    have hh := (hp.map g).sum_eq.trans totals.2.1
    simpa only [(bases a b c).1,F,Matrix.cons_val_zero] using hh
  have fresh : g k=A x y z := by simpa only [k,size,(bases a b c).1,F,Matrix.cons_val_zero] using totals.2.2
  have hA : 1 ≤ A x y z := by
    have hh := (chain_values a b c a ha hb hc ha).1 0
    rw [(bases a b c).1] at hh
    exact hh.1
  have hN : 0 ≤ N := by
    have hh := (chain_values a b c a ha hb hc ha).1 0
    rw [(bases a b c).1] at hh
    change 1 ≤ A x y z ∧ A x y z<N at hh
    omega
  have end4 : K x y z-A x y z+((P 3).map f).sum+f (k-1)=0 := by
    dsimp [l] at oldzero
    simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton] at oldzero
    nlinarith only [h1,h2,h3,oldzero]
  have end4n : SW x y z-2*A x y z+((P 3).map g).sum+g (k-1)= -A x y z := by
    dsimp [l] at newold
    simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton] at newold
    nlinarith only [h1n,h2n,h3n,newold]
  have h3n' : Rp+((P 2).map g).sum+g (a+c+b-1)=SW x y z-2*A x y z := h3n
  obtain ⟨w1,w1n,w2,w2n⟩ := hfirst
  have ho : InStrip f (N/2) 0 l := by
    apply four_windows_strip f (N/2) N (P 0) (P 1) (P 2) (P 3)
      (a-1) (a+c-1) (a+c+b-1) (k-1) E R (K x y z-A x y z)
      (B x y) (L x z) (K x y z) (A x y z) (by omega) (by omega)
      (fun i hi => (hpos 0 i hi).1) (fun i hi => (hpos 1 i hi).1)
      (fun i hi => (hpos 2 i hi).1) (fun i hi => (hpos 3 i hi).1)
      h1 h2 h3 end4 (step 0).1 (step 1).1 (step 2).1 (step 3).1
      w1 w2 hW (by dsimp [Window]; omega)
  let Pn := fun j : Fin 4 =>
    if early && decide (j=2) || (!early && decide (j=3)) then P j++[k] else P j
  have hpn (j : Fin 4) (i : ℕ) (hi : i ∈ Pn j) : 0 ≤ g i := by
    dsimp [Pn] at hi
    split_ifs at hi
    · rcases List.mem_append.mp hi with hi|hi
      · exact (hpos j i hi).2
      · rw [List.mem_singleton.mp hi,fresh]; omega
    · exact (hpos j i hi).2
  have hn : InStrip g N 0
      (Pn 0++[a-1]++Pn 1++[a+c-1]++Pn 2++[a+c+b-1]++Pn 3++[k-1]) := by
    apply four_windows_strip g N (2*N+1) (Pn 0) (Pn 1) (Pn 2) (Pn 3)
      (a-1) (a+c-1) (a+c+b-1) (k-1) Ep Rp
      (SW x y z-2*A x y z+(if early then A x y z else 0))
      (SU x y) (SV x z) (SW x y z) (A x y z) hN (by omega)
      (hpn 0) (hpn 1) (hpn 2) (hpn 3)
      (by cases early <;> simpa [Pn] using h1n)
      (by cases early <;> simpa [Pn] using h2n)
      (by cases early <;> simp [Pn,List.map_append,List.sum_append,fresh] <;> omega)
      (by cases early <;> simp [Pn,List.map_append,List.sum_append,fresh] <;> omega)
      (step 0).2 (step 1).2 (step 2).2 (step 3).2 w1n w2n hWn (by dsimp [Window]; omega)
  cases early
  · let pre := P 0++[a-1]++P 1++[a+c-1]++P 2++[a+c+b-1]++P 3
    let post := [k-1]
    apply realize_split a b c ha hb hc pre post
    · simpa only [pre,post,List.append_assoc] using hp
    · simpa only [pre,post,l,List.append_assoc] using ho
    · simpa [pre,post,Pn,List.append_assoc] using hn
  · let pre := P 0++[a-1]++P 1++[a+c-1]++P 2
    let post := [a+c+b-1]++P 3++[k-1]
    apply realize_split a b c ha hb hc pre post
    · simpa only [pre,post,List.append_assoc] using hp
    · simpa only [pre,post,l,List.append_assoc] using ho
    · simpa [pre,post,Pn,List.append_assoc] using hn

private def moderateHighBanks (a b c h : ℕ) : Fin 4 → List ℕ :=
  ![stock a b c a 0 (full a b c a 0)++lowV c a,
    highComplement c a h,
    stock a b c a 2 (full a b c a 2)++highV c a h,
    stock a b c a 3 (full a b c a 3)]

private theorem moderate_high_inventory (a b c h : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hca : a ≤ c) :
    let P := moderateHighBanks a b c h
    (P 0++[a-1]++P 1++[a+c-1]++P 2++[a+c+b-1]++P 3++[a+b+c+a-1]).Perm
      (List.range (a+b+c+a)) := by
  have hs := Multiset.coe_eq_coe.mpr (high_split c a h)
  have hv := congrArg (fun l : List ℕ => (l:Multiset ℕ)) (v_inventory a b c a hca (by omega))
  simp only [←Multiset.coe_add] at hs hv
  dsimp only
  apply Multiset.coe_eq_coe.mp
  rw [←canonical_inventory a b c a ha hb (by omega) ha]
  dsimp [moderateHighBanks]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  rw [←hv,←hs]
  ac_rfl

private theorem moderate_high_positive (a b c h : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hca : a ≤ c)
    (j : Fin 4) (i : ℕ) (hi : i ∈ moderateHighBanks a b c h j) :
    0 ≤ oldValue a b c a i ∧ 0 ≤ newValue a b c a i := by
  have inV (mask i : ℕ) (hi : i ∈ highV c a mask) :
      i ∈ stock a b c a 1 (full a b c a 1) := by
    obtain ⟨e,he,_,rfl⟩ := (chamberLabels_mem _ _ _ _).mp hi
    rw [stock,full,chamberLabels_full]
    simp only [chainLength,chainStart,Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons]
    apply List.mem_range'_1.mpr
    omega
  have inLo (i : ℕ) (hi : i ∈ lowV c a) :
      i ∈ stock a b c a 1 (full a b c a 1) := by
    obtain ⟨e,he,_,rfl⟩ := (chamberLabels_mem _ _ _ _).mp hi
    rw [stock,full,chamberLabels_full]
    simp only [chainLength,chainStart,Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons]
    apply List.mem_range'_1.mpr
    omega
  fin_cases j <;> dsimp [moderateHighBanks,highComplement] at hi
  all_goals try (rcases List.mem_append.mp hi with hi|hi)
  all_goals first
    | exact stock_nonnegative a b c ha hb (by omega) _ _ i hi
    | exact stock_nonnegative a b c ha hb (by omega) 1 _ i (inV _ i hi)
    | exact stock_nonnegative a b c ha hb (by omega) 1 _ i (inLo i hi)

private theorem moderate_high_masses (a b c h : ℕ) (ha : 2 ≤ a) (hca : a ≤ c)
    (hh : h < 2^(a-1)) (f : ℕ → ℤ) (H : Fin 4 → ℤ)
    (hf : ∀ j : Fin 4, ∀ e < chainLength a b c a j-1,
      f (chainStart b c a j+e)=2^e*H j) :
    let C := fun j : Fin 4 => (full a b c a j : ℤ)
    let m : ℤ := 2^(c-a)
    let P := moderateHighBanks a b c h
    ((P 0).map f).sum=C 0*H 0+(m-1)*H 1 ∧
    ((P 1).map f).sum=m*(C 0-h)*H 1 ∧
    ((P 2).map f).sum=C 2*H 2+m*h*H 1 ∧
    ((P 3).map f).sum=C 3*H 3 := by
  have hfull (j : Fin 4) : full a b c a j < 2^(chainLength a b c a j-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c a j-1); omega
  have mU := stock_mass a b c a 0 _ (hfull 0) f H hf
  have mW := stock_mass a b c a 2 _ (hfull 2) f H hf
  have mX := stock_mass a b c a 3 _ (hfull 3) f H hf
  have mH := high_mass a b c a h hca (by omega) hh f H hf
  have mHF := high_mass a b c a (2^(a-1)-1) hca (by omega)
    (by have := Nat.two_pow_pos (a-1); omega) f H hf
  have mHC := ((high_split c a h).map f).sum_eq
  simp only [List.map_append,List.sum_append,mH,mHF] at mHC
  have mLo : ((lowV c a).map f).sum=((2:ℤ)^(c-a)-1)*H 1 := by
    have hm : 2^(c-a)-1 < 2^(c-a) := by have := Nat.two_pow_pos (c-a); omega
    have hx := chamberLabels_sum (c-a) a (2^(c-a)-1) hm f (H 1)
      (fun e he => by simpa only [chainStart,Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons] using hf 1 e (by simp [chainLength]; omega))
    simpa only [lowV,Nat.cast_sub (show 1 ≤ 2^(c-a) by have := Nat.two_pow_pos (c-a); omega),
      Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hx
  dsimp only [moderateHighBanks]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,List.map_append,List.sum_append,mU,mW,mX,mLo,mH]
  refine ⟨trivial,?_,trivial,trivial⟩
  dsimp [full,chainLength] at mHC ⊢
  nlinarith only [mHC]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
