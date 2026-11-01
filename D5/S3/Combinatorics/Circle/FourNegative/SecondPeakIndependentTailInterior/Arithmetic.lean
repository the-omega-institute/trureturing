/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Arithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Arithmetic
   mirror-E: none(waiver:private-consumed-coordinate-bridges)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Exact physical mask weights and native-to-rational coordinate bridges. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Supports
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Chart0
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Chart1
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
open private Parameters Parameters.a Parameters.b Parameters.c Parameters.d
  Parameters.hc Parameters.hd Parameters.ha Parameters.hb r s v parameter_eqs dyadic_eqs from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Parameters
open private lengths offsets uSupport vSupport wSupport xSupport support nativeMask native_total
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Supports
open private qMask qExpr chartExpr from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Model
open private chart0_nonnegative from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Chart0
open private chart1_nonnegative from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Chart1
open scoped BigOperators

private def modelMask (p : Parameters) : Fin 4 → Fin 4 → ℚ :=
  qMask (2^p.c) (2^p.d) (2^(r p)) (2^(s p))
    (if p.c = 2 then 2*2^(v p)-1 else 2*2^(v p)) 1 (2^(s p)-1) (3*2^(s p))
private def modelExpr (p : Parameters) (row kind bank : Fin 4) : ℚ :=
  qExpr (2^p.c) (2^p.d) (2^(r p)) (2^(s p))
    (if p.c = 2 then 2*2^(v p)-1 else 2*2^(v p)) 1 (2^(s p)-1) (3*2^(s p)) row kind bank

private theorem sum_range_q (n : ℕ) :
    (∑ e ∈ Finset.range n, (2 : ℚ)^e) = 2^n-1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

private theorem native_cast (p : Parameters) (j chain : Fin 4) :
    (nativeMask p j chain : ℚ) = ∑ e ∈ support p j chain, (2 : ℚ)^e := by
  simp only [nativeMask,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat]

private theorem native_total_q (p : Parameters) (chain : Fin 4) :
    (nativeMask p 0 chain : ℚ) + nativeMask p 1 chain +
      nativeMask p 2 chain + nativeMask p 3 chain = 2^(lengths p chain)-1 := by
  have h := congrArg (fun n : ℕ => (n : ℚ)) (native_total p chain)
  have hp : 1 ≤ (2 : ℕ)^(lengths p chain) := by have := Nat.two_pow_pos (lengths p chain); omega
  simpa only [Nat.cast_add,Nat.cast_sub hp,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using h

private theorem two_half (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℚ)^(n-1) = 2^n/2 := by
  have h : (2 : ℚ)^n = 2^(n-1)*2 := by
    conv_lhs => rw [show n = (n-1)+1 by omega,pow_succ]
  rw [h]; ring

private theorem mask_coordinates (p : Parameters) (j chain : Fin 4) :
    (nativeMask p j chain : ℚ) = modelMask p j chain := by
  have hc := p.hc; have hd := p.hd; have ha := p.ha; have hb := p.hb
  obtain ⟨heA,heB,heD⟩ := parameter_eqs p
  obtain ⟨hw,hx,hy,hu⟩ := dyadic_eqs p
  have hU0 : (nativeMask p 0 0 : ℚ) =
      if p.c = 2 then 2*2^(v p)-1 else 2*2^(v p) := by
    rw [native_cast]
    by_cases h : p.c = 2
    · have he : p.d-3 = p.d-p.c-1 := by omega
      simp [support,uSupport,h,sum_range_q,he,hu]
    · simp [support,uSupport,h,hu]
  have hU2 : (nativeMask p 2 0 : ℚ) = 2^p.d/8 := by
    rw [native_cast]
    change (∑ e ∈ ({p.d-3} : Finset ℕ), (2 : ℚ)^e) = _
    rw [Finset.sum_singleton]
    have he : p.d = (p.d-3)+3 := by omega
    conv_rhs => rw [he,pow_add]
    norm_num; ring
  have hU3 : (nativeMask p 3 0 : ℚ) = 0 := by
    simp [native_cast,support,uSupport]
  have hV0 : (nativeMask p 0 1 : ℚ) = (2 : ℚ)^p.c/2-1 := by
    rw [native_cast]
    simpa [support,vSupport,sum_range_q,two_half p.c (by omega)]
  have hV1 : (nativeMask p 1 1 : ℚ) = 0 := by simp [native_cast,support,vSupport]
  have hV2 : (nativeMask p 2 1 : ℚ) = 0 := by simp [native_cast,support,vSupport]
  have hV3 : (nativeMask p 3 1 : ℚ) = 0 := by simp [native_cast,support,vSupport]
  have hW1 : (nativeMask p 1 2 : ℚ) = 0 := by simp [native_cast,support,wSupport]
  have hX0 : (nativeMask p 0 3 : ℚ) =
      (2 : ℚ)^(r p)*(2^p.d+3*2^p.c+2) := by
    rw [native_cast]
    change (∑ e ∈ ({r p+p.d,r p+p.c+1,r p+p.c,r p+1} : Finset ℕ), (2 : ℚ)^e) = _
    rw [Finset.sum_insert (by simp; omega),Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp; omega),Finset.sum_singleton]
    simp only [pow_add,pow_one]; ring
  have hX1 : (nativeMask p 1 3 : ℚ) = (2 : ℚ)^(r p)*2^p.c*2^p.d := by
    rw [native_cast]
    simp [support,xSupport,pow_add,mul_assoc]
  have hX3 : (nativeMask p 3 3 : ℚ) = 1 := by
    simp [native_cast,support,xSupport]
  have hW0 : (nativeMask p 0 2 : ℚ) = (2 : ℚ)^(s p)-1 := by
    rw [native_cast]
    simp [support,wSupport,sum_range_q]
  have hW2 : (nativeMask p 2 2 : ℚ) = 3*(2 : ℚ)^(s p) := by
    rw [native_cast]
    change (∑ e ∈ ({s p,s p+1} : Finset ℕ), (2 : ℚ)^e) = _
    rw [Finset.sum_insert (by simp),Finset.sum_singleton,pow_succ]
    ring
  have totalU := native_total_q p 0
  have totalW := native_total_q p 2
  have totalX := native_total_q p 3
  dsimp only [lengths] at totalU totalW totalX
  rw [two_half p.d (by omega)] at totalU
  rw [two_half p.b (by omega),hy] at totalW
  rw [two_half p.a (by omega),hx] at totalX
  fin_cases chain <;> fin_cases j <;>
    dsimp [modelMask,qMask] <;>
    first | exact hU0 | exact hU2 | exact hU3 | exact hV0 | exact hV1 |
      exact hV2 | exact hV3 | exact hW1 | exact hW0 | exact hW2 | exact hX0 |
      exact hX1 | exact hX3 | linarith

private theorem model_nonnegative (p : Parameters) (row kind bank : Fin 4)
    (hr : row.val < 2) (hk : kind.val < 2) :
    0 ≤ modelExpr p row kind bank := by
  let V : ℚ := 2^(v p)-1
  let T : ℚ := 2^(r p)-1
  let R : ℚ := 2^(s p)-1
  have power_one (n : ℕ) : (1:ℚ) ≤ 2^n := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) (Nat.zero_le n)
  have hV : 0 ≤ V := by dsimp [V]; linarith [power_one (v p)]
  have hT : 0 ≤ T := by dsimp [T]; linarith [power_one (r p)]
  have hR : 0 ≤ R := by dsimp [R]; linarith [power_one (s p)]
  have hw := (dyadic_eqs p).1
  by_cases hc : p.c = 2
  · convert chart0_nonnegative 0 V T R (by norm_num) hV hT hR row kind bank hr hk using 1 <;>
      simp [modelExpr,chartExpr,V,T,R,hw,hc]
  · let Z : ℚ := 2^p.c-8
    have hZ : 0 ≤ Z := by
      have hc3 : 3 ≤ p.c := by have := p.hc; omega
      have hp := pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) hc3
      norm_num at hp
      dsimp [Z]; linarith
    convert chart1_nonnegative Z V T R hZ hV hT hR row kind bank hr hk using 1 <;>
      simp [modelExpr,chartExpr,Z,V,T,R,hw,hc]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
