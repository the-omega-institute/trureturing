/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Arithmetic
   generality: I
   mirror-B: none(waiver:owning-blueprint-scribe)
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
  roundingD roundingW roundingEps native_X0 native_W0 power_sub_q
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Supports
open private qMask qExpr qExpr_affine evenChartExpr boundaryChartExpr from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Model
open private chart0_nonnegative from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Chart0
open private chart1_nonnegative from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Chart1
open scoped BigOperators

private def modelMask (p : Parameters) : Fin 4 → Fin 4 → ℚ :=
  qMask (2^p.c) (2^p.d) (2^(r p)) (2^(s p))
    (if p.c = 2 then 2*2^(v p)-1 else 2*2^(v p)) (roundingD p) (roundingW p)
private def modelExpr (p : Parameters) (row kind bank : Fin 4) : ℚ :=
  qExpr (2^p.c) (2^p.d) (2^(r p)) (2^(s p))
    (if p.c = 2 then 2*2^(v p)-1 else 2*2^(v p)) (roundingD p) (roundingW p) row kind bank

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
  have hX0 : (nativeMask p 0 3 : ℚ) = roundingD p := native_X0 p
  have hX1 : (nativeMask p 1 3 : ℚ) = (2 : ℚ)^(r p)*2^p.c*2^p.d/8 := by
    rw [native_cast]
    change (∑ e ∈ ({p.a-3} : Finset ℕ), (2 : ℚ)^e) = _
    rw [Finset.sum_singleton,power_sub_q p.a 3 (by omega),hx]
    norm_num
  have hX3 : (nativeMask p 3 3 : ℚ) = 1 := by
    simp [native_cast,support,xSupport]
  have hW0 : (nativeMask p 0 2 : ℚ) = roundingW p := native_W0 p
  have hW3 : (nativeMask p 3 2 : ℚ) = (2 : ℚ)^p.b/2-4*2^(s p) := by
    rw [native_cast]
    change (∑ e ∈ Finset.range (p.b-1) \ Finset.range (s p+2), (2 : ℚ)^e) = _
    have hsub : Finset.range (s p+2) ⊆ Finset.range (p.b-1) := by
      intro e he
      simp only [Finset.mem_range] at he ⊢
      dsimp [s] at he
      omega
    rw [Finset.sum_sdiff_eq_sub hsub,sum_range_q,sum_range_q,two_half p.b (by omega),pow_add]
    norm_num
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
      exact hV2 | exact hV3 | exact hW1 | exact hW0 | exact hW3 | exact hX0 |
      exact hX1 | exact hX3 | linarith

private theorem even_nonnegative (mode : Fin 2) (Z V T R K : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hK1 : 1 ≤ K) (hK4 : K ≤ 4)
    (row kind bank : Fin 4) (hr : row.val < 2) (hk : kind.val < 2) :
    let z := if mode = 0 then 4 else Z+8
    let w := 4*z*(V+1)
    let u := if mode = 0 then 2*(V+1)-1 else 2*(V+1)
    0 ≤ qExpr z w (2*(T+1)) (R+1) u
      ((T+1)*(w+3*z+2)/4-(K-1)/2) (K*(R+1)-1) row kind bank := by
  let z : ℚ := if mode = 0 then 4 else Z+8
  let w : ℚ := 4*z*(V+1)
  let u : ℚ := if mode = 0 then 2*(V+1)-1 else 2*(V+1)
  let D : ℚ := (T+1)*(w+3*z+2)/4
  let h : ℚ := (K-1)/3
  have h0 : 0 ≤ qExpr z w (2*(T+1)) (R+1) u D ((R+1)-1) row kind bank := by
    have h := chart0_nonnegative mode 0 Z V T R hZ hV hT hR row kind bank hr hk
    norm_num [evenChartExpr] at h
    exact h
  have h1 : 0 ≤ qExpr z w (2*(T+1)) (R+1) u (D-3/2) (4*(R+1)-1) row kind bank := by
    have h := chart0_nonnegative mode 1 Z V T R hZ hV hT hR row kind bank hr hk
    norm_num [evenChartExpr] at h
    exact h
  have hh : 0 ≤ h := by dsimp [h]; linarith
  have hh1 : 0 ≤ 1-h := by dsimp [h]; linarith
  have he := qExpr_affine z w (2*(T+1)) (R+1) u D (D-3/2) ((R+1)-1)
    (4*(R+1)-1) h row kind bank
  have heD : (1-h)*D+h*(D-3/2) = D-(K-1)/2 := by dsimp [h]; ring
  have heW : (1-h)*((R+1)-1)+h*(4*(R+1)-1) = K*(R+1)-1 := by dsimp [h]; ring
  rw [heD,heW] at he
  change 0 ≤ qExpr z w (2*(T+1)) (R+1) u (D-(K-1)/2) (K*(R+1)-1) row kind bank
  rw [he]
  exact add_nonneg (mul_nonneg hh1 h0) (mul_nonneg hh h1)

private theorem model_nonnegative (p : Parameters) (row kind bank : Fin 4)
    (hr : row.val < 2) (hk : kind.val < 2) :
    0 ≤ modelExpr p row kind bank := by
  let V : ℚ := 2^(v p)-1
  let R : ℚ := 2^(s p)-1
  have power_one (n : ℕ) : (1:ℚ) ≤ 2^n := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) (Nat.zero_le n)
  have hV : 0 ≤ V := by dsimp [V]; linarith [power_one (v p)]
  have hR : 0 ≤ R := by dsimp [R]; linarith [power_one (s p)]
  have hw := (dyadic_eqs p).1
  have hc := p.hc
  by_cases h0 : r p = 0
  · by_cases hc2 : p.c = 2
    · convert chart1_nonnegative 0 0 0 V R (by norm_num) hV hR row kind bank hr hk using 1 <;>
        simp [modelExpr,boundaryChartExpr,roundingD,roundingW,V,R,hw,h0,hc2]
    · by_cases hc3 : p.c = 3
      · by_cases hs : s p = 0
        · convert chart1_nonnegative 1 1 0 V R (by norm_num) hV hR row kind bank hr hk using 1 <;>
            simp [modelExpr,boundaryChartExpr,roundingD,roundingW,roundingEps,V,R,hw,h0,hc2,hc3,hs] <;> (congr 1 <;> ring)
        · convert chart1_nonnegative 1 0 0 V R (by norm_num) hV hR row kind bank hr hk using 1 <;>
            simp [modelExpr,boundaryChartExpr,roundingD,roundingW,roundingEps,V,R,hw,h0,hc2,hc3,hs] <;> (congr 1 <;> ring)
      · let Z : ℚ := 2^p.c-16
        have hZ : 0 ≤ Z := by
          have hc4 : 4 ≤ p.c := by omega
          have hp := pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) hc4
          norm_num at hp
          dsimp [Z]; linarith
        by_cases hs : s p = 0
        · convert chart1_nonnegative 2 1 Z V R hZ hV hR row kind bank hr hk using 1 <;>
            simp [modelExpr,boundaryChartExpr,roundingD,roundingW,roundingEps,Z,V,R,hw,h0,hc2,hc3,hs] <;> (congr 1 <;> ring)
        · convert chart1_nonnegative 2 0 Z V R hZ hV hR row kind bank hr hk using 1 <;>
            simp [modelExpr,boundaryChartExpr,roundingD,roundingW,roundingEps,Z,V,R,hw,h0,hc2,hc3,hs] <;> (congr 1 <;> ring)
  · let T : ℚ := 2^(r p-1)-1
    have hT : 0 ≤ T := by dsimp [T]; linarith [power_one (r p-1)]
    have ht : (2 : ℚ)^(r p) = 2 * 2^(r p-1) := by
      have he : r p = (r p-1)+1 := by omega
      conv_lhs => rw [he,pow_succ]
      ring
    let K : ℚ := if r p = 1 then (if p.c = 2 then 4 else 2) else if r p = 2 then 3 else 1
    have hK1 : 1 ≤ K := by dsimp [K]; split_ifs <;> norm_num
    have hK4 : K ≤ 4 := by dsimp [K]; split_ifs <;> norm_num
    have hD : roundingD p = (2 : ℚ)^(r p-1)*(2^p.d+3*2^p.c+2)/4-(K-1)/2 := by
      by_cases h1 : r p = 1
      · by_cases hc2 : p.c = 2 <;> simp [roundingD,K,h0,h1,hc2] <;> ring
      · by_cases h2 : r p = 2
        · simp [roundingD,K,h0,h1,h2]; ring
        · simp [roundingD,K,h0,h1,h2,ht]; ring
    have hW : roundingW p = K*(2 : ℚ)^(s p)-1 := by
      dsimp [roundingW,K]
      split_ifs <;> simp_all
    by_cases hc2 : p.c = 2
    · convert even_nonnegative 0 0 V T R K (by norm_num) hV hT hR hK1 hK4 row kind bank hr hk using 1 <;>
        simp [modelExpr,V,T,R,hw,hc2,hD,hW,ht]
    · let Z : ℚ := 2^p.c-8
      have hZ : 0 ≤ Z := by
        have hc3 : 3 ≤ p.c := by omega
        have hp := pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) hc3
        norm_num at hp
        dsimp [Z]; linarith
      convert even_nonnegative 1 Z V T R K hZ hV hT hR hK1 hK4 row kind bank hr hk using 1 <;>
        simp [modelExpr,Z,V,T,R,hw,hc2,hD,hW,ht]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
