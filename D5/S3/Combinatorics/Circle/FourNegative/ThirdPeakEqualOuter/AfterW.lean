/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/AfterW
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: ThirdPeakEqualOuter AfterW for the complete original physical family. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Source

/-! ThirdPeakEqualOuter: AfterW. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
open SourceWidth PeriodicShortening RunFirstEarTransport
open private A B L K SU SV SW Window AfterWWindows
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Arithmetic
open private F G nextF nextG bases positive_rows terminal_rows native_rows stock_nonnegative
  four_windows_strip Joint realize_split
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Source
open private size sourceMod base chainLength chainStart oldValue newValue chain_values
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private full stock complement terminals stock_split canonical_inventory
  stock_mass complement_mass
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks

private def afterWBanks (a b c r v : ℕ) : Fin 4 → List ℕ :=
  ![complement a b c a 1 (v-1),
    stock a b c a 2 (full a b c a 2)++stock a b c a 0 (r-1),
    stock a b c a 3 (full a b c a 3),
    complement a b c a 0 (r-1)++stock a b c a 1 (v-1)]

private def afterWTerminals (a b c : ℕ) : Fin 4 → ℕ :=
  ![a+c-1,a+c+b-1,a+b+c+a-1,a-1]

private theorem afterW_inventory (a b c r v : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    let P := afterWBanks a b c r v
    let T := afterWTerminals a b c
    (P 0++[T 0]++P 1++[T 1]++P 2++[T 2]++P 3++[T 3]).Perm
      (List.range (a+b+c+a)) := by
  have hu := Multiset.coe_eq_coe.mpr (stock_split a b c a 0 (r-1))
  have hv := Multiset.coe_eq_coe.mpr (stock_split a b c a 1 (v-1))
  simp only [←Multiset.coe_add] at hu hv
  dsimp only
  apply Multiset.coe_eq_coe.mp
  rw [←canonical_inventory a b c a ha hb hc ha]
  dsimp [afterWBanks,afterWTerminals]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  rw [←hu,←hv]
  ac_rfl

private theorem afterW_nonnegative (a b c r v : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (j : Fin 4) (i : ℕ) (hi : i ∈ afterWBanks a b c r v j) :
    0 ≤ oldValue a b c a i ∧ 0 ≤ newValue a b c a i := by
  fin_cases j <;> dsimp [afterWBanks,complement] at hi
  all_goals try (rcases List.mem_append.mp hi with hi|hi)
  all_goals exact stock_nonnegative a b c ha hb hc _ _ i hi

private theorem afterW_masses (a b c r v : ℕ)
    (hr : 1 ≤ r) (hrcap : r ≤ 2^(a-1)) (hv : 1 ≤ v) (hvcap : v ≤ 2^(c-1))
    (f : ℕ → ℤ) (H : Fin 4 → ℤ)
    (hf : ∀ j : Fin 4, ∀ e < chainLength a b c a j-1,
      f (chainStart b c a j+e)=2^e*H j) :
    let C := fun j : Fin 4 => (full a b c a j : ℤ)
    let P := afterWBanks a b c r v
    ((P 0).map f).sum=(C 1-(v-1:ℤ))*H 1 ∧
    ((P 1).map f).sum=C 2*H 2+(r-1:ℤ)*H 0 ∧
    ((P 2).map f).sum=C 3*H 3 ∧
    ((P 3).map f).sum=(C 0-(r-1:ℤ))*H 0+(v-1:ℤ)*H 1 := by
  have hru : r-1 < 2^(chainLength a b c a 0-1) := by simp [chainLength]; omega
  have hvu : v-1 < 2^(chainLength a b c a 1-1) := by simp [chainLength]; omega
  have hfull (j : Fin 4) : full a b c a j < 2^(chainLength a b c a j-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c a j-1); omega
  have ur := stock_mass a b c a 0 (r-1) hru f H hf
  have uc := complement_mass a b c a 0 (r-1) hru f H hf
  have vr := stock_mass a b c a 1 (v-1) hvu f H hf
  have vc := complement_mass a b c a 1 (v-1) hvu f H hf
  have wf := stock_mass a b c a 2 _ (hfull 2) f H hf
  have xf := stock_mass a b c a 3 _ (hfull 3) f H hf
  dsimp only
  simp only [afterWBanks,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,List.map_append,List.sum_append,ur,uc,vr,vc,wf,xf,
    Nat.cast_sub hr,Nat.cast_sub hv,Nat.cast_one]
  trivial

set_option maxHeartbeats 1600000 in
private theorem afterW_realize (a b c r v : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hr : 1 ≤ r) (hrcap : r ≤ 2^(a-1)) (hv : 1 ≤ v) (hvcap : v ≤ 2^(c-1))
    (windows : AfterWWindows (2^a) (2^b) (2^c) r v) : Joint a b c := by
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let N := sourceMod a b c a
  let f := oldValue a b c a
  let g := newValue a b c a
  let P := afterWBanks a b c r v
  let T := afterWTerminals a b c
  let C := fun j : Fin 4 => (full a b c a j : ℤ)
  let δ := (r:ℤ)*A x y z-(v:ℤ)*B x y
  let ε := 2*(r:ℤ)*A x y z-(v:ℤ)*SU x y
  have mo := afterW_masses a b c r v hr hrcap hv hvcap f (F x y z)
    (positive_rows a b c ha hb hc).1
  have mn := afterW_masses a b c r v hr hrcap hv hvcap g (G x y z)
    (positive_rows a b c ha hb hc).2
  change ((P 0).map f).sum=(C 1-((v:ℤ)-1))*B x y ∧
    ((P 1).map f).sum=C 2*L x z+((r:ℤ)-1)*A x y z ∧
    ((P 2).map f).sum=C 3*K x y z ∧
    ((P 3).map f).sum=(C 0-((r:ℤ)-1))*A x y z+((v:ℤ)-1)*B x y at mo
  change ((P 0).map g).sum=(C 1-((v:ℤ)-1))*SU x y ∧
    ((P 1).map g).sum=C 2*SV x z+((r:ℤ)-1)*(2*A x y z) ∧
    ((P 2).map g).sum=C 3*SW x y z ∧
    ((P 3).map g).sum=(C 0-((r:ℤ)-1))*(2*A x y z)+((v:ℤ)-1)*SU x y at mn
  have nu := native_rows a b c ha hb hc 0
  have nv := native_rows a b c ha hb hc 1
  have nw := native_rows a b c ha hb hc 2
  have nx := native_rows a b c ha hb hc 3
  dsimp only [F,G,nextF,nextG,terminals] at nu nv nw nx
  change C 0*A x y z+f (a-1)=B x y-A x y z ∧
    C 0*(2*A x y z)+g (a-1)=SU x y-2*A x y z ∧
    2*f (a-1)=B x y-N ∧ 2*g (a-1)=SU x y-(2*N+1) at nu
  change C 1*B x y+f (T 0)=L x z-B x y ∧
    C 1*SU x y+g (T 0)=SV x z-SU x y ∧
    2*f (T 0)=L x z-N ∧ 2*g (T 0)=SV x z-(2*N+1) at nv
  change C 2*L x z+f (T 1)=K x y z-L x z ∧
    C 2*SV x z+g (T 1)=SW x y z-SV x z ∧
    2*f (T 1)=K x y z-N ∧ 2*g (T 1)=SW x y z-(2*N+1) at nw
  change C 3*K x y z+f (T 2)=A x y z-K x y z ∧
    C 3*SW x y z+g (T 2)=A x y z-SW x y z ∧
    2*f (T 2)=A x y z-N ∧ 2*g (T 2)=A x y z-(2*N+1) at nx
  have fresh : g (a+b+c+a)=A x y z := by
    have hh := (chain_values a b c a ha hb hc ha).2.2.2
    simpa only [size,(bases a b c).1,F,Matrix.cons_val_zero] using hh
  have hA : 0 ≤ A x y z := by dsimp [A,x,y,z]; positivity
  have hN : 0 ≤ N := by
    have hh := (chain_values a b c a ha hb hc ha).1 0
    rw [(bases a b c).1] at hh
    change 1 ≤ A x y z ∧ A x y z<N at hh
    omega
  obtain ⟨w1,w2,w3,w4,w1n,w2n,w3n,w4n⟩ := windows
  have ho : InStrip f (N/2) 0
      (P 0++[T 0]++P 1++[T 1]++P 2++[T 2]++P 3++[T 3]) := by
    apply four_windows_strip f (N/2) N (P 0) (P 1) (P 2) (P 3)
      (T 0) (T 1) (T 2) (T 3) (L x z-v*B x y) (K x y z-A x y z+δ) δ
      (L x z) (K x y z) (A x y z) (B x y) (by omega) (by omega)
      (fun i hi => (afterW_nonnegative a b c r v ha hb hc 0 i hi).1)
      (fun i hi => (afterW_nonnegative a b c r v ha hb hc 1 i hi).1)
      (fun i hi => (afterW_nonnegative a b c r v ha hb hc 2 i hi).1)
      (fun i hi => (afterW_nonnegative a b c r v ha hb hc 3 i hi).1)
      (by nlinarith only [mo.1,nv.1])
      (by dsimp [δ]; nlinarith only [mo.2.1,nw.1])
      (by nlinarith only [mo.2.2.1,nx.1])
      (by dsimp [δ,T,afterWTerminals]; nlinarith only [mo.2.2.2,nu.1])
      nv.2.2.1 nw.2.2.1 nx.2.2.1 nu.2.2.1 w1 w2 w3 w4
  have hn : InStrip g N 0
      (P 0++[T 0]++P 1++[T 1]++([a+b+c+a]++P 2)++[T 2]++P 3++[T 3]) := by
    apply four_windows_strip g N (2*N+1) (P 0) (P 1) ([a+b+c+a]++P 2) (P 3)
      (T 0) (T 1) (T 2) (T 3) (SV x z-v*SU x y) (SW x y z-2*A x y z+ε) ε
      (SV x z) (SW x y z) (A x y z) (SU x y) hN (by omega)
      (fun i hi => (afterW_nonnegative a b c r v ha hb hc 0 i hi).2)
      (fun i hi => (afterW_nonnegative a b c r v ha hb hc 1 i hi).2) ?_
      (fun i hi => (afterW_nonnegative a b c r v ha hb hc 3 i hi).2)
      (by nlinarith only [mn.1,nv.2.1])
      (by dsimp [ε]; nlinarith only [mn.2.1,nw.2.1])
      (by simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,fresh];
          nlinarith only [mn.2.2.1,nx.2.1])
      (by dsimp [ε,T,afterWTerminals]; nlinarith only [mn.2.2.2,nu.2.1])
      nv.2.2.2 nw.2.2.2 nx.2.2.2 nu.2.2.2 w1n w2n w3n w4n
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · rw [List.mem_singleton.mp hi,fresh]; exact hA
    · exact (afterW_nonnegative a b c r v ha hb hc 2 i hi).2
  let pre := P 0++[T 0]++P 1++[T 1]
  let post := P 2++[T 2]++P 3++[T 3]
  apply realize_split a b c ha hb hc pre post
  · simpa only [pre,post,List.append_assoc] using afterW_inventory a b c r v ha hb hc
  · simpa only [pre,post,List.append_assoc] using ho
  · simpa only [pre,post,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using hn

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
