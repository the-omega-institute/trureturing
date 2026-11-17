/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Masses
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Exact paired source sums for all three nested W banks and both complementary banks. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Source

/-! Every coefficient is the mass of its actual physical occurrence list. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private bank from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Source
open private Submask submask_xor full_submask from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Dilation
open private chain_values from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (base newBase chainLength chainStart oldValue newValue)

private theorem bank_masses (a b c alpha M v J : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (haCap : alpha<2^(a-1)) (hmCap : M<2^(b-1)) (hvCap : v<2^(c-1))
    (hj : Submask J M) :
    ∀ side : Bool,
    let F := if side then newBase a b c c else base a b c c
    let f := if side then newValue a b c c else oldValue a b c c
    let uf : ℤ := ((2^(c-1)-1:ℕ):ℤ)
    let wf : ℤ := ((2^(b-1)-1:ℕ):ℤ)
    let xf : ℤ := ((2^(a-1)-1:ℕ):ℤ)
    let P := bank a b c alpha M v J
    ((P 0).map f).sum=(wf-M)*F 2+alpha*F 3 ∧
    ((P 1).map f).sum=(xf-alpha)*F 3+(M-J)*F 2+v*F 1 ∧
    ((P 2).map f).sum=uf*F 0 ∧
    ((P 3).map f).sum=(uf-v)*F 1+J*F 2 := by
  intro side
  dsimp only
  let F := if side then newBase a b c c else base a b c c
  let f := if side then newValue a b c c else oldValue a b c c
  have tab := chain_values a b c c ha hb hc hc
  have series (r : Fin 4) : ∀ i<chainLength a b c c r-1,
      f (chainStart b c c r+i)=2^i*F r := by
    intro i hi
    cases side
    · exact (tab.2.1 r i (by omega)).trans (if_pos (by omega))
    · exact (tab.2.2.1 r i (by omega)).trans (if_pos (by omega))
  have wseries : ∀ i<b-1, f (c+c+i)=2^i*F 2 := by
    simpa [chainLength,chainStart] using series 2
  have xseries : ∀ i<a-1, f (c+c+b+i)=2^i*F 3 := by
    simpa [chainLength,chainStart] using series 3
  have vseries : ∀ i<c-1, f (c+i)=2^i*F 1 := by
    simpa [chainLength,chainStart] using series 1
  have hMJ := submask_xor J M hj
  have hjCap : J<2^(b-1) := by omega
  have fullcap (n : ℕ) : 2^n-1<2^n :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have old_complement (n m : ℕ) (hm : m<2^n) :
      (((2^n-1) ^^^ m:ℕ):ℤ)=((2^n-1:ℕ):ℤ)-(m:ℤ) := by
    have h := congrArg (fun t : ℕ => (t:ℤ)) (submask_xor m (2^n-1) (full_submask n m hm))
    push_cast at h
    omega
  have mj : ((M ^^^ J:ℕ):ℤ)=(M:ℤ)-(J:ℤ) := by
    have h := congrArg (fun t : ℕ => (t:ℤ)) hMJ
    push_cast at h
    omega
  have wm := chamberLabels_sum (b-1) (c+c) ((2^(b-1)-1) ^^^ M)
    (Nat.xor_lt_two_pow (fullcap _) hmCap) f (F 2) wseries
  have wj := chamberLabels_sum (b-1) (c+c) (M ^^^ J)
    (Nat.xor_lt_two_pow hmCap hjCap) f (F 2) wseries
  have wlast := chamberLabels_sum (b-1) (c+c) J hjCap f (F 2) wseries
  have xa := chamberLabels_sum (a-1) (c+c+b) alpha haCap f (F 3) xseries
  have xc := chamberLabels_sum (a-1) (c+c+b) ((2^(a-1)-1) ^^^ alpha)
    (Nat.xor_lt_two_pow (fullcap _) haCap) f (F 3) xseries
  have vv := chamberLabels_sum (c-1) c v hvCap f (F 1) vseries
  have vc := chamberLabels_sum (c-1) c ((2^(c-1)-1) ^^^ v)
    (Nat.xor_lt_two_pow (fullcap _) hvCap) f (F 1) vseries
  have uu : ((List.range' 0 (c-1)).map f).sum=((2^(c-1)-1:ℕ):ℤ)*F 0 := by
    rw [←chamberLabels_full]
    apply chamberLabels_sum _ _ _ (fullcap _)
    simpa [chainLength,chainStart] using series 0
  change ((bank a b c alpha M v J 0).map f).sum = _ ∧
    ((bank a b c alpha M v J 1).map f).sum = _ ∧
    ((bank a b c alpha M v J 2).map f).sum = _ ∧
    ((bank a b c alpha M v J 3).map f).sum = _
  simp only [F,bank,List.map_append,List.sum_append,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    wm,wj,wlast,xa,xc,vv,vc,uu,
    old_complement (b-1) M hmCap,old_complement (a-1) alpha haCap,
    old_complement (c-1) v hvCap,mj,and_self]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
