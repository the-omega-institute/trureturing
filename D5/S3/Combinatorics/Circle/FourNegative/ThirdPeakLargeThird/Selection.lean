/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/Selection
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Exhaustive original-domain selection and consumption of all eight proved windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.DiagonalMasks

/-! ThirdPeakLargeThird: Selection. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
open SourceWidth
open private A B L K H SU SV SW window quotient remainder large_head quotient_remainder
  third_windows regionII_windows regionIII_windows
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Arithmetic
open private diagonal_windows from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.DiagonalArithmetic
open private selectedV dictionary dyadic_parameters strict_dyadic double_gap_dyadic selected_properties
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Parameters
open private paidP paid_branches paid_available paid_submask
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.DiagonalMasks
open private rowBase rowHeads rowDoubles physical_source
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Physical
open private word cut from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Banks
open private size base newBase sourceMod oldValue newValue chain_values new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private insertAt from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

private theorem tail_windows (a b c d : ℕ)
    (hb : 2≤b) (hba : b≤a) (had : a<d) (hdc : d+3≤c) :
    let v:=selectedV a b c d
    window ((2*(v:ℤ)+1)*base a b c d 1-base a b c d 2) (base a b c d 0) ∧
    window ((2*(v:ℤ)+1)*newBase a b c d 1-newBase a b c d 2) (base a b c d 0) ∧
    window 0 (base a b c d 1) ∧ window 0 (newBase a b c d 1) := by
  dsimp only
  have dp:=dyadic_parameters a b c d hb hba had hdc
  have props:=selected_properties a b c d hb hba had hdc
  have dic:=dictionary a b c d
  have tab:=chain_values a b c d (by omega) hb (by omega) (by omega)
  have nb:=new_base_bounds a b c d (by omega) hb (by omega) (by omega)
  have bb : 0<B (2^a) (2^b) (2^d) := by
    have hh:=(tab.1 1).1
    rw [dic.1] at hh
    change 1≤B (2^a) (2^b) (2^d) at hh
    omega
  have big:=(large_head (2^a) (2^b) (2^c) (2^d) dp.1 dp.2.1 dp.2.2.1 dp.2.2.2).1
  have rem:=quotient_remainder (2^a) (2^b) (2^c) (2^d) bb
  rw [←props.2.2.1] at rem
  have ww:=third_windows (2^a) (2^b) (2^c) (2^d) (selectedV a b c d:ℤ) bb big
    (by exact_mod_cast (show 0≤selectedV a b c d by omega)) props.2.2.2 rem
  refine ⟨?_,?_,?_,?_⟩
  · convert ww.1 using 1 <;> simp [remainder,dic.1] <;> ring
  · convert ww.2 using 1
    · rw [dic.2]
      dsimp [SU,SV,remainder]
      ring
    · simp [dic.1]
  · have hh:=(tab.1 1).1;exact ⟨by omega,by omega⟩
  · have hh:=(nb 1).1;exact ⟨by omega,by omega⟩

set_option maxHeartbeats 2400000 in
private theorem selected_source (a b c d : ℕ)
    (hb : 2≤b) (hba : b≤a) (had : a<d) (hdc : d+3≤c) :
    ∃ l : List ℕ,l.Perm (List.range (size a b c d)) ∧
      InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 l ∧
      ∃ j : ℕ,j≤size a b c d ∧
        InStrip (newValue a b c d) (sourceMod a b c d) 0 (insertAt (size a b c d) l j) := by
  have props:=selected_properties a b c d hb hba had hdc
  have dp:=dyadic_parameters a b c d hb hba had hdc
  have dic:=dictionary a b c d
  have tail:=tail_windows a b c d hb hba had hdc
  by_cases hab : b<a
  · have hx:=strict_dyadic b a hab
    have ht:=strict_dyadic a d had
    have ww:=regionII_windows (2^a) (2^b) (2^c) (2^d) dp.1 hx ht dp.2.2.2
    have hw : ∀ side r,window (rowDoubles a b c d (selectedV a b c d) 0 true false side r)
        (rowHeads a b c d true side r) := by
      intro side r
      cases side <;> fin_cases r
      · convert ww.1 using 1 <;> simp [rowDoubles,rowHeads,rowBase,dic.1] <;> ring
      · convert ww.2.2.1 using 1 <;> simp [rowDoubles,rowHeads,rowBase,dic.1] <;> ring
      · simpa [rowDoubles,rowHeads,rowBase] using tail.1
      · simpa [rowDoubles,rowHeads,rowBase] using tail.2.2.1
      · convert ww.2.1 using 1 <;> simp [rowDoubles,rowHeads,rowBase,dic.2] <;> ring
      · convert ww.2.2.2 using 1 <;> simp [rowDoubles,rowHeads,rowBase,dic.1,dic.2] <;> ring
      · simpa [rowDoubles,rowHeads,rowBase] using tail.2.1
      · simpa [rowDoubles,rowHeads,rowBase] using tail.2.2.2
    have data:=physical_source a b c d (selectedV a b c d) 0 true false
      (by omega) hb (by omega) (by omega) props.2.1 (by positivity) (by simp) hw
    exact ⟨word a b c d (selectedV a b c d) 0 true,data.1,data.2.1,
      cut a b c d (selectedV a b c d) 0 true false,data.2.2.1.le,data.2.2.2⟩
  · have hEq : b=a := by omega
    subst b
    by_cases hsep : a+2≤d
    · have ht:=double_gap_dyadic a d hsep
      have hx : (4:ℤ)≤2^a := dp.1
      have ww:=regionIII_windows (2^a) (2^c) (2^d) hx ht dp.2.2.2
      have hw : ∀ side r,window (rowDoubles a a c d (selectedV a a c d) 0 false false side r)
          (rowHeads a a c d false side r) := by
        intro side r
        cases side <;> fin_cases r
        · convert ww.1 using 1 <;> simp [rowDoubles,rowHeads,rowBase,dic.1] <;> ring
        · convert ww.2.2.1 using 1 <;> simp [rowDoubles,rowHeads,rowBase,dic.1] <;> ring
        · simpa [rowDoubles,rowHeads,rowBase] using tail.1
        · simpa [rowDoubles,rowHeads,rowBase] using tail.2.2.1
        · convert ww.2.1 using 1 <;> simp [rowDoubles,rowHeads,rowBase,dic.2] <;> ring
        · convert ww.2.2.2 using 1 <;> simp [rowDoubles,rowHeads,rowBase,dic.2] <;> ring
        · simpa [rowDoubles,rowHeads,rowBase] using tail.2.1
        · simpa [rowDoubles,rowHeads,rowBase] using tail.2.2.2
      have data:=physical_source a a c d (selectedV a a c d) 0 false false
        hb hb (by omega) (by omega) props.2.1 (by positivity) (by simp) hw
      exact ⟨word a a c d (selectedV a a c d) 0 false,data.1,data.2.1,
        cut a a c d (selectedV a a c d) 0 false false,data.2.2.1.le,data.2.2.2⟩
    · have hd : d=a+1 := by omega
      subst d
      have hc : a+4≤c := by omega
      have hx : (4:ℤ)≤2^a := dp.1
      have hz : 16*(2:ℤ)^a≤2^c := by
        have hh:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hc
        have he : (2:ℤ)^(a+4)=16*2^a := by rw [pow_add];norm_num;ring
        rwa [he] at hh
      have tEq : (2:ℤ)^(a+1)=2*(2:ℤ)^a := by rw [pow_succ];ring
      have branches:=paid_branches a c
      have ww:=diagonal_windows (2^a) (2^c) (paidP a c:ℤ) hx hz (by positivity) branches
      have hw : ∀ side r,window
          (rowDoubles a a c (a+1) (selectedV a a c (a+1)) (paidP a c) false true side r)
          (rowHeads a a c (a+1) false side r) := by
        intro side r
        cases side <;> fin_cases r
        · convert ww.1 using 1 <;> simp [rowDoubles,rowHeads,rowBase,dic.1,tEq] <;> ring
        · convert ww.2.2.1 using 1 <;> simp [rowDoubles,rowHeads,rowBase,dic.1,tEq] <;> ring
        · simpa [rowDoubles,rowHeads,rowBase] using tail.1
        · simpa [rowDoubles,rowHeads,rowBase] using tail.2.2.1
        · convert ww.2.1 using 1 <;> simp [rowDoubles,rowHeads,rowBase,dic.2,tEq] <;> ring
        · convert ww.2.2.2 using 1 <;>
            simp [rowDoubles,rowHeads,rowBase,dic.1,dic.2,tEq] <;> ring
        · simpa [rowDoubles,rowHeads,rowBase] using tail.2.1
        · simpa [rowDoubles,rowHeads,rowBase] using tail.2.2.2
      have data:=physical_source a a c (a+1) (selectedV a a c (a+1)) (paidP a c) false true
        hb hb (by omega) (by omega) props.2.1 (paid_available a c hc) (paid_submask a c hb hc) hw
      exact ⟨word a a c (a+1) (selectedV a a c (a+1)) (paidP a c) false,data.1,data.2.1,
        cut a a c (a+1) (selectedV a a c (a+1)) (paidP a c) false true,data.2.2.1.le,data.2.2.2⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
