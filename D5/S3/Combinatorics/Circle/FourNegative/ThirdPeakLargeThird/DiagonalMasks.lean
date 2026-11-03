/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/DiagonalMasks
   generality: I
   mirror-B: none(source-only-unelaborated-draft)
   mirror-E: none(source-only-unelaborated-draft)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Exhaustive dyadic thresholds and literal payment-bit containment in the selected V mask. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Parameters

/-! Unelaborated source. Numeric p≤v is never used to infer sparse containment.
The proof explicitly exhibits v=2^r*(2*x^2-1)+q, q<2^r, and reads bit r. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
open private quotient from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Arithmetic
open private payment_decomposition from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.DiagonalArithmetic
open private selectedV selected_properties from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Parameters

private def paidP (a c : ℕ) : ℕ := if c≤3*a+1 then 0 else 2^(c-3*a-2)

private theorem paid_branches (a c : ℕ) :
    ((paidP a c:ℤ)=0 ∧ (2:ℤ)^c≤2*((2:ℤ)^a)^3) ∨
    (1≤(paidP a c:ℤ) ∧ (2:ℤ)^c=4*(paidP a c:ℤ)*((2:ℤ)^a)^3) := by
  by_cases hs : c≤3*a+1
  · left
    have hh:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hs
    have he : (2:ℤ)^(3*a+1)=2*((2:ℤ)^a)^3 := by
      rw [show 3*a+1=a+a+a+1 by omega]
      simp only [pow_add,pow_one]
      ring
    exact ⟨by simp [paidP,hs],by rwa [he] at hh⟩
  · right
    have hp : 1≤(paidP a c:ℤ) := by
      simp only [paidP,if_neg hs,Nat.cast_pow,Nat.cast_ofNat]
      exact one_le_pow₀ (by norm_num)
    refine ⟨hp,?_⟩
    simp only [paidP,if_neg hs,Nat.cast_pow,Nat.cast_ofNat]
    have he : c=(c-3*a-2)+a+a+a+2 := by omega
    conv_lhs => rw [he]
    simp only [pow_add]
    norm_num
    ring

private theorem paid_value (a c : ℕ) (hc : 3*a+2≤c) :
    paidP a c=(2:ℕ)^c/(4*((2:ℕ)^a)^3) ∧ paidP a c=2^(c-3*a-2) := by
  have hs : ¬c≤3*a+1 := by omega
  have hp : paidP a c=2^(c-3*a-2) := by simp [paidP,hs]
  have hz : (2:ℕ)^c=paidP a c*(4*((2:ℕ)^a)^3) := by
    rw [hp]
    have he : c=(c-3*a-2)+a+a+a+2 := by omega
    conv_lhs => rw [he]
    simp only [pow_add]
    norm_num
    ring
  refine ⟨?_,hp⟩
  rw [hz]
  simp

private theorem paid_available (a c : ℕ) (hc : a+4≤c) : paidP a c<2^(c-1) := by
  by_cases hs : c≤3*a+1
  · simp [paidP,hs]
  · simp only [paidP,if_neg hs]
    exact Nat.pow_lt_pow_right (by decide : 1<2) (by omega)

private theorem paid_submask (a c : ℕ) (ha : 2≤a) (hc : a+4≤c) :
    ∀ e<c-1,(paidP a c).testBit e=true → (selectedV a a c (a+1)).testBit e=true := by
  by_cases hs : c≤3*a+1
  · simp [paidP,hs]
  · let x : ℤ:=2^a
    let z : ℤ:=2^c
    let p:=paidP a c
    let r:=c-3*a-2
    have hp : p=2^r := by
      simpa [p,r] using (paid_value a c (by omega)).2
    have branches:=paid_branches a c
    have ppos : 1≤(p:ℤ) := by rw [hp];push_cast;exact one_le_pow₀ (by norm_num)
    have hz : z=4*(p:ℤ)*x^3 := by
      rcases branches with h|h
      · change (p:ℤ)=0 ∧ _ at h
        omega
      · exact h.2
    have hx : 4≤x := by
      have hh:=pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha
      simpa [x] using hh
    have props:=selected_properties a a c (a+1) ha (by omega) (by omega) (by omega)
    have hcast : (selectedV a a c (a+1):ℤ)=quotient x x z (2*x) := by
      have he : (2:ℤ)^(a+1)=2*x := by dsimp [x];rw [pow_succ];ring
      simpa [x,z,he] using props.2.2.1
    obtain ⟨q,hq0,hqp,hvq⟩:=payment_decomposition x z (p:ℤ) hx ppos hz
    let qn:=q.toNat
    have hqn : (qn:ℤ)=q := Int.toNat_of_nonneg hq0
    have qsmall : qn<2^r := by
      have hh : (qn:ℤ)<(p:ℤ) := by omega
      have hh' : qn<p := by exact_mod_cast hh
      rwa [hp] at hh'
    let xn : ℕ:=2^a
    have xn4 : 4≤xn := by exact_mod_cast hx
    have coeffpos : 1≤2*xn^2 := by
      have hh : 0<xn^2 := by positivity
      omega
    have coeffcast : ((2*xn^2-1:ℕ):ℤ)=2*x^2-1 := by
      rw [Nat.cast_sub coeffpos]
      simp [xn,x]
    have vnat : selectedV a a c (a+1)=2^r*(2*xn^2-1)+qn := by
      apply Int.ofNat_inj.mp
      calc
        (selectedV a a c (a+1):ℤ)=(p:ℤ)*(2*x^2-1)+q := hcast.trans hvq
        _ = ((2^r*(2*xn^2-1)+qn:ℕ):ℤ) := by
          rw [Nat.cast_add,Nat.cast_mul,coeffcast,hqn,←hp]
    have oddcoeff : (2*xn^2-1).testBit 0=true := by
      simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.pow_zero,Nat.div_one]
      have hh : 1≤2*xn^2 := coeffpos
      have hm : (2*xn^2-1)%2=1 := by omega
      simp [hm]
    intro e he hbit
    have hr : r=e := of_decide_eq_true (by simpa only [hp,Nat.testBit_two_pow] using hbit)
    subst e
    rw [vnat,Nat.testBit_two_pow_mul_add (2*xn^2-1) qsmall r]
    simpa using oddcoeff

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
