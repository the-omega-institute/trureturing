/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualOuter/Source
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: ThirdPeakEqualOuter Source for the complete original physical family. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Source

/-! ThirdPeakEqualOuter: Source. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
open SourceWidth PeriodicShortening RunFirstEarTransport
open private A B L K SU SV SW Window
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Arithmetic
open private size seed sourceMod base newBase charge chainLength chainStart
  nextBase nextNewBase oldValue newValue chain_values source_signs source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private full stock complement terminals stock_split canonical_inventory
  stock_good stock_mass complement_mass
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private Gates four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
open private Margin
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Arithmetic
open private gates_of_margins
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Source
open private actual_nat_joint_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

private def F (x y z : ℤ) : Fin 4 → ℤ := ![A x y z,B x y,L x z,K x y z]
private def G (x y z : ℤ) : Fin 4 → ℤ := ![2*A x y z,SU x y,SV x z,SW x y z]
private def nextF (x y z : ℤ) : Fin 4 → ℤ := ![B x y,L x z,K x y z,A x y z]
private def nextG (x y z : ℤ) : Fin 4 → ℤ := ![SU x y,SV x z,SW x y z,A x y z]

private theorem bases (a b c : ℕ) :
    base a b c a=F (2^a) (2^b) (2^c) ∧
    newBase a b c a=G (2^a) (2^b) (2^c) ∧
    nextBase a b c a=nextF (2^a) (2^b) (2^c) ∧
    nextNewBase a b c a=nextG (2^a) (2^b) (2^c) := by
  repeat' constructor
  all_goals funext i
  all_goals fin_cases i <;> dsimp [F,G,nextF,nextG,A,B,L,K,SU,SV,SW,
    base,newBase,charge,nextBase,nextNewBase] <;> ring

private theorem positive_rows (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    (∀ r : Fin 4, ∀ e < chainLength a b c a r-1,
      oldValue a b c a (chainStart b c a r+e)=2^e*F (2^a) (2^b) (2^c) r) ∧
    (∀ r : Fin 4, ∀ e < chainLength a b c a r-1,
      newValue a b c a (chainStart b c a r+e)=2^e*G (2^a) (2^b) (2^c) r) := by
  have h := chain_values a b c a ha hb hc ha
  constructor
  · intro r e he
    rw [h.2.1 r e (by omega),if_pos (by omega),(bases a b c).1]
  · intro r e he
    rw [h.2.2.1 r e (by omega),if_pos (by omega),(bases a b c).2.1]

private theorem terminal_rows (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (r : Fin 4) :
    let f := oldValue a b c a
    let g := newValue a b c a
    let T := terminals a b c a r
    let P := stock a b c a r (full a b c a r)
    let N := sourceMod a b c a
    (P.map f).sum+f T=nextF (2^a) (2^b) (2^c) r-F (2^a) (2^b) (2^c) r ∧
    (P.map g).sum+g T=nextG (2^a) (2^b) (2^c) r-G (2^a) (2^b) (2^c) r ∧
    2*f T=nextF (2^a) (2^b) (2^c) r-N ∧
    2*g T=nextG (2^a) (2^b) (2^c) r-(2*N+1) := by
  dsimp only
  have hfull : full a b c a r < 2^(chainLength a b c a r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c a r-1); omega
  rw [stock_mass a b c a r _ hfull _ _ (positive_rows a b c ha hb hc).1,
    stock_mass a b c a r _ hfull _ _ (positive_rows a b c ha hb hc).2]
  have ht : terminals a b c a r=chainStart b c a r+(chainLength a b c a r-1) := by
    fin_cases r <;> simp [terminals,chainStart,chainLength] <;> omega
  rw [ht]
  simpa only [full,(bases a b c).1,(bases a b c).2.1,
    (bases a b c).2.2.1,(bases a b c).2.2.2] using native_masses a b c a ha hb hc ha r

private theorem stock_nonnegative (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (r : Fin 4) (mask i : ℕ) (hi : i ∈ stock a b c a r mask) :
    0 ≤ oldValue a b c a i ∧ 0 ≤ newValue a b c a i := by
  obtain ⟨hi',hn⟩ := stock_good a b c a ha hb hc ha r mask i hi
  have hs := source_signs a b c a ha hb hc ha i hi'
  rw [if_neg hn] at hs
  exact ⟨hs.1.le,hs.2.le⟩

private theorem native_rows (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (r : Fin 4) :
    let C : ℤ := full a b c a r
    let f := oldValue a b c a
    let g := newValue a b c a
    let T := terminals a b c a r
    C*F (2^a) (2^b) (2^c) r+f T=nextF (2^a) (2^b) (2^c) r-F (2^a) (2^b) (2^c) r ∧
    C*G (2^a) (2^b) (2^c) r+g T=nextG (2^a) (2^b) (2^c) r-G (2^a) (2^b) (2^c) r ∧
    2*f T=nextF (2^a) (2^b) (2^c) r-sourceMod a b c a ∧
    2*g T=nextG (2^a) (2^b) (2^c) r-(2*sourceMod a b c a+1) := by
  have h := terminal_rows a b c ha hb hc r
  dsimp only at h ⊢
  have hcap : full a b c a r < 2^(chainLength a b c a r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c a r-1); omega
  rw [stock_mass a b c a r _ hcap _ _ (positive_rows a b c ha hb hc).1,
    stock_mass a b c a r _ hcap _ _ (positive_rows a b c ha hb hc).2] at h
  exact h

private theorem four_windows_strip (f : ℕ → ℤ) (C D : ℤ)
    (P1 P2 P3 P4 : List ℕ) (t1 t2 t3 t4 : ℕ) (e1 e2 e3 h1 h2 h3 h4 : ℤ)
    (hC : 0 ≤ C) (hD : D ≤ 2*C+1)
    (pos1 : ∀ i ∈ P1, 0 ≤ f i) (pos2 : ∀ i ∈ P2, 0 ≤ f i)
    (pos3 : ∀ i ∈ P3, 0 ≤ f i) (pos4 : ∀ i ∈ P4, 0 ≤ f i)
    (end1 : (P1.map f).sum+f t1=e1)
    (end2 : e1+(P2.map f).sum+f t2=e2)
    (end3 : e2+(P3.map f).sum+f t3=e3)
    (end4 : e3+(P4.map f).sum+f t4=0)
    (step1 : 2*f t1=h1-D) (step2 : 2*f t2=h2-D)
    (step3 : 2*f t3=h3-D) (step4 : 2*f t4=h4-D)
    (w1 : Window e1 h1) (w2 : Window e2 h2)
    (w3 : Window e3 h3) (w4 : Window 0 h4) :
    InStrip f C 0 (P1++[t1]++P2++[t2]++P3++[t3]++P4++[t4]) := by
  apply four_strip f C P1 P2 P3 P4 t1 t2 t3 t4 pos1 pos2 pos3 pos4
  apply gates_of_margins hC hD end1 end2 end3 end4 step1 step2 step3 step4
  · simpa only [Margin,Window,sub_nonneg] using w1
  · simpa only [Margin,Window,sub_nonneg] using w2
  · simpa only [Margin,Window,sub_nonneg] using w3
  · simpa only [Margin,Window,sub_nonneg] using w4

private def Joint (a b c : ℕ) : Prop :=
  ∃ sigma : List (Fin (a+b+c+a)), ∃ j : ℕ, j ≤ a+b+c+a ∧
    OriginalOrder (a+b+c+a) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
    OriginalOrder (a+b+c+a+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
      (earWord (a+b+c+a) sigma j)

private theorem realize_split (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (pre post : List ℕ) (hp : (pre++post).Perm (List.range (a+b+c+a)))
    (ho : InStrip (oldValue a b c a) (sourceMod a b c a/2) 0 (pre++post))
    (hn : InStrip (newValue a b c a) (sourceMod a b c a) 0 (pre++(a+b+c+a)::post)) :
    Joint a b c := by
  apply (actual_nat_joint_iff a b c a ha hb hc ha).mpr
  have hlen := hp.length_eq
  simp only [List.length_append,List.length_range] at hlen
  refine ⟨pre++post,hp,ho,pre.length,by dsimp [size]; omega,?_⟩
  simpa only [insertAt,List.take_append_of_le_length (le_refl pre.length),
    List.drop_append_of_le_length (le_refl pre.length),List.take_length,List.drop_length,
    List.nil_append] using hn

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
