/- GID: D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound
   mirror-E: none(waiver:unbounded-analytic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Stirling]
   utility: none
   digest: A uniform strict binomial-ratio bound for every n at least 496. -/

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.NatFactorial

open Filter Real
open scoped Topology

set_option autoImplicit false

namespace D5.S3.Arith.FactorialRatio.GridAntidiagonalTrafficBound

/-- The logarithmic Stirling envelope is below one at every large-gap parity peak. -/
private theorem uniform_peak_bound : ∀ n a k e : ℕ, 1 ≤ a → 16 ≤ k →
    (e = 1 → 17 ≤ k) → e ≤ 1 → 2*a+k = n → n+e = 2*k*(k+1) →
    (a : ℝ)*((n : ℝ)-2*a+1)/((n : ℝ)-1)*(Nat.choose n a : ℝ)^2 /
      (Nat.choose (2*n-2) (n-1) : ℝ) < 1 := by
  have upper (m : ℕ) (hm : 0 < m) :
      Real.log (m.factorial : ℝ) ≤ (m : ℝ) * Real.log m - m +
        Real.log m / 2 + Real.log (2 * Real.pi) / 2 + 1 / (12 * m) := by
    let q : ℕ → ℝ := fun j => Real.log (Stirling.stirlingSeq (j + 1)) -
      1 / (12 * ((j : ℝ) + 1))
    have hq : Monotone q := by
      apply monotone_nat_of_le_succ
      intro j
      have hs := Stirling.log_stirlingSeq_sdiff_le (j + 1)
      have hr : (1 : ℝ) / (12 * ((j : ℝ) + 1) * ((j : ℝ) + 2)) =
          1 / (12 * ((j : ℝ) + 1)) - 1 / (12 * ((j : ℝ) + 2)) := by
        field_simp
        <;> ring
      dsimp [q]
      push_cast at hs ⊢
      rw [show (j : ℝ) + 1 + 1 = (j : ℝ) + 2 by ring] at hs ⊢
      linarith
    have hl : Tendsto (fun j : ℕ => Real.log (Stirling.stirlingSeq (j + 1)))
        atTop (𝓝 (Real.log (Real.sqrt Real.pi))) :=
      (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
        (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1))
    have hr : Tendsto (fun j : ℕ => 1 / (12 * ((j : ℝ) + 1))) atTop (𝓝 0) := by
      convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 12 using 1
      · ext j; field_simp
      · norm_num
    have hlim : Tendsto q atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
      simpa only [sub_zero] using hl.sub hr
    have hb := hq.ge_of_tendsto hlim (m - 1)
    have hm' : m - 1 + 1 = m := by omega
    dsimp [q] at hb
    have hc : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hm'
    rw [hm', hc, Stirling.log_stirlingSeq_formula,
      Real.log_div (by positivity) (by positivity), Real.log_exp,
      Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity)] at hb
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne']
    linarith
  let h : ℝ → ℝ := fun x => (1-x)*Real.log (1-x)+(1+x)*Real.log (1+x)-x^2
  have entropy (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) : x^2 ≤
      (1-x)*Real.log (1-x)+(1+x)*Real.log (1+x) := by
    have hd (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
        HasDerivAt h (Real.log ((1+y)/(1-y))-2*y) y := by
      have hm : 1-y ≠ 0 := by linarith [hy.2]
      have hp : 1+y ≠ 0 := by linarith [hy.1]
      convert! (((hasDerivAt_const y 1).sub (hasDerivAt_id y)).mul
        (((hasDerivAt_const y 1).sub (hasDerivAt_id y)).log hm)).add
        (((hasDerivAt_const y 1).add (hasDerivAt_id y)).mul
        (((hasDerivAt_const y 1).add (hasDerivAt_id y)).log hp)) |>.sub
        ((hasDerivAt_id y).pow 2) using 1
      rw [Real.log_div hp hm]
      dsimp only [Pi.sub_apply, Pi.add_apply, id_eq]
      field_simp
      <;> ring
    have mono : MonotoneOn h (Set.Ico 0 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
        (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
        (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      intro y hy
      have hy' := interior_subset hy
      have hh := Real.sum_range_le_log_div hy'.1 hy'.2 1
      norm_num at hh
      linarith
    have hh := mono (by norm_num) ⟨hx,hx1⟩ hx
    dsimp [h] at hh
    norm_num at hh
    linarith
  let L : ℝ → ℝ → ℝ := fun n k => Real.log 4 + Real.log n + Real.log (k+1) -
    Real.log (n+k) - Real.log Real.pi/2 - Real.log (n-1)/2 - k^2/n +
    1/(6*n)+1/(6*(n-1))
  let T : ℕ → ℕ → ℝ := fun n a =>
    (a : ℝ)*((n : ℝ)-2*a+1)/((n : ℝ)-1) * (Nat.choose n a : ℝ)^2 /
      (Nat.choose (2*n-2) (n-1) : ℝ)
  have tpos (n a : ℕ) (ha : 1 ≤ a) (han : 2*a < n) : 0 < T n a := by
    have hn : 2 ≤ n := by omega
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have han' : (2 : ℝ)*a < n := by exact_mod_cast han
    have hc : (0 : ℝ) < Nat.choose n a := by exact_mod_cast Nat.choose_pos (by omega : a ≤ n)
    have hd : (0 : ℝ) < Nat.choose (2*n-2) (n-1) := by
      exact_mod_cast Nat.choose_pos (by omega : n-1 ≤ 2*n-2)
    dsimp [T]
    have : 0 < (n : ℝ)-2*a+1 := by linarith
    have : 0 < (n : ℝ)-1 := by linarith
    positivity
  have logchoose (m r : ℕ) (hr : r ≤ m) :
      Real.log (Nat.choose m r : ℝ) = Real.log (m.factorial : ℝ) -
        Real.log (r.factorial : ℝ) - Real.log ((m-r).factorial : ℝ) := by
    rw [Nat.cast_choose ℝ hr, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    ring
  have envelope (n a : ℕ) (ha : 1 ≤ a) (han : 2*a < n) :
      Real.log (T n a) ≤ L n ((n : ℝ)-2*a) := by
    have hn : 2 ≤ n := by omega
    have hna : a ≤ n := by omega
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have han' : (2 : ℝ)*a < n := by exact_mod_cast han
    have hb : (0 : ℝ) < n-a := by linarith
    have hm : (0 : ℝ) < n-1 := by linarith
    have hk : (0 : ℝ) < n-2*a+1 := by linarith
    have hc : (0 : ℝ) < Nat.choose n a := by exact_mod_cast Nat.choose_pos hna
    have hc' : (0 : ℝ) < Nat.choose (2*n-2) (n-1) := by
      exact_mod_cast Nat.choose_pos (by omega : n-1 ≤ 2*n-2)
    have hlT : Real.log (T n a) = Real.log a + Real.log ((n : ℝ)-2*a+1) -
        Real.log ((n : ℝ)-1) + 2*Real.log (n.factorial : ℝ) -
        2*Real.log (a.factorial : ℝ) - 2*Real.log ((n-a).factorial : ℝ) +
        2*Real.log ((n-1).factorial : ℝ) - Real.log ((2*n-2).factorial : ℝ) := by
      dsimp [T]
      rw [Real.log_div (by positivity) hc'.ne',
        Real.log_mul (by positivity) (by positivity),
        Real.log_div (by positivity) hm.ne', Real.log_mul ha'.ne' hk.ne', Real.log_pow,
        logchoose n a hna, logchoose (2*n-2) (n-1) (by omega),
        show 2*n-2-(n-1) = n-1 by omega]
      ring
    have hent := entropy (((n : ℝ)-2*a)/n) (by positivity)
      ((div_lt_one (by linarith)).mpr (by linarith))
    have he1 : 1-((n : ℝ)-2*a)/n = 2*a/n := by field_simp; ring
    have he2 : 1+((n : ℝ)-2*a)/n = 2*((n : ℝ)-a)/n := by field_simp; ring
    rw [he1,he2, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) ha'.ne',
      Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) hb.ne'] at hent
    have hent' := mul_le_mul_of_nonneg_left hent (show (0 : ℝ) ≤ n by positivity)
    have heq : (n : ℝ)*((((n : ℝ)-2*a)/n)^2) = ((n : ℝ)-2*a)^2/n := by
      field_simp
    have heq' : (n : ℝ)*(2*a/n*(Real.log 2+Real.log a-Real.log n)+
        (2*((n : ℝ)-a)/n)*(Real.log 2+Real.log ((n : ℝ)-a)-Real.log n)) =
        2*a*Real.log a+2*((n : ℝ)-a)*Real.log ((n : ℝ)-a)-2*n*Real.log n+
          2*n*Real.log 2 := by field_simp; ring
    rw [heq,heq'] at hent'
    have un := upper n (by omega)
    have um := upper (n-1) (by omega)
    have la := Stirling.le_log_factorial_stirling (n := a) (by omega)
    have lb := Stirling.le_log_factorial_stirling (n := n-a) (by omega)
    have lm := Stirling.le_log_factorial_stirling (n := 2*n-2) (by omega)
    have c1 : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    have c2 : ((n-a : ℕ) : ℝ) = (n : ℝ)-a := by rw [Nat.cast_sub hna]
    have c3 : ((2*n-2 : ℕ) : ℝ) = 2*((n : ℝ)-1) := by
      push_cast [Nat.cast_sub (by omega : 2 ≤ 2*n)]; ring
    rw [c1] at um
    rw [c2] at lb
    rw [c3,Real.log_mul (by norm_num) hm.ne'] at lm
    have lnk : Real.log ((n : ℝ)+((n : ℝ)-2*a)) = Real.log 2+Real.log ((n : ℝ)-a) := by
      rw [show (n : ℝ)+((n : ℝ)-2*a)=2*((n : ℝ)-a) by ring,
        Real.log_mul (by norm_num) hb.ne']
    have l4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
      norm_num
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne'] at un um la lb lm
    rw [hlT]
    dsimp [L]
    rw [lnk,l4]
    have rn : 1/(6*(n : ℝ)) = 2*(1/(12*n)) := by ring
    have rm : 1/(6*((n : ℝ)-1)) = 2*(1/(12*((n : ℝ)-1))) := by field_simp; norm_num
    linarith only [un,um,la,lb,lm,hent',rn,rm]
  let N : ℕ → ℝ → ℝ := fun e k => 2*k*(k+1)-e
  let C : ℕ → ℝ → ℝ := fun e k => Real.log (N e k) + Real.log (k+1) -
    Real.log (N e k+k) - Real.log (N e k-1)/2 - k^2/N e k
  have npos (e : ℕ) (he : e ≤ 1) (k : ℝ) (hk : 3 ≤ k) : 1 < N e k := by
    have he' : (e : ℝ) ≤ 1 := by exact_mod_cast he
    dsimp [N]; nlinarith
  have canti (e : ℕ) (he : e ≤ 1) : AntitoneOn (C e) (Set.Ici 3) := by
    let d : ℕ → ℝ → ℝ := fun e k => (4*k+2)/N e k+1/(k+1)-(4*k+3)/(N e k+k)-
      (4*k+2)/(2*(N e k-1))-(2*k*N e k-k^2*(4*k+2))/(N e k)^2
    have hd (k : ℝ) (hk : k ∈ Set.Ici 3) : HasDerivAt (C e) (d e k) k := by
      change 3 ≤ k at hk
      have hn := npos e he k hk
      have h1 : k+1 ≠ 0 := by linarith [hk]
      have h2 : N e k+k ≠ 0 := by linarith [hk]
      have h3 : N e k-1 ≠ 0 := by linarith
      have hn' : N e k ≠ 0 := by linarith
      have hN : HasDerivAt (N e) (4*k+2) k := by
        convert! (((hasDerivAt_id k).const_mul 2).mul
          ((hasDerivAt_id k).add_const 1)).sub_const (e : ℝ) using 1 <;> dsimp [N] <;> ring
      convert! ((((hN.log hn').add (((hasDerivAt_id k).add_const 1).log h1)).sub
        ((hN.add (hasDerivAt_id k)).log h2)).sub
        (((hN.sub_const 1).log h3).div_const 2)).sub
        (((hasDerivAt_id k).pow 2).div hN hn') using 1
      dsimp [d]; field_simp; ring
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 3)
      (fun k hk => (hd k hk).continuousAt.continuousWithinAt)
      (fun k hk => (hd k (interior_subset hk)).hasDerivWithinAt)
    intro k hk
    have hk' : 3 ≤ k := interior_subset hk
    have hn := npos e he k hk'
    have h1 : 0 < k+1 := by linarith
    have h2 : 0 < N e k+k := by linarith
    have h3 : 0 < N e k-1 := by linarith
    have hn' : 0 < N e k := by linarith
    interval_cases e
    · have heq : d 0 k = -(4*k^3+20*k^2+28*k+11) /
          (2*(k+1)^2*(2*k+3)*(2*k^2+2*k-1)) := by
        dsimp [d,N]
        norm_num only [Nat.cast_zero, sub_zero]
        field_simp (disch := nlinarith only [hk'])
        <;> ring
      rw [heq]
      apply div_nonpos_of_nonpos_of_nonneg
      · have : 0 ≤ 4*k^3+20*k^2+28*k+11 := by positivity
        linarith
      · have : 0 ≤ 2*k^2+2*k-1 := by nlinarith only [hk',sq_nonneg k]
        positivity
    · have heq : d 1 k = -(8*k^7+48*k^6+80*k^5+12*k^4-52*k^3-3*k^2+20*k-5) /
          (2*(k+1)*(k^2+k-1)*(2*k^2+2*k-1)^2*(2*k^2+3*k-1)) := by
        dsimp [d,N]
        norm_num only [Nat.cast_one]
        field_simp (disch := nlinarith only [hk'])
        <;> ring
      rw [heq]
      apply div_nonpos_of_nonpos_of_nonneg
      · have hp : 8*k^7+48*k^6+80*k^5+12*k^4-52*k^3-3*k^2+20*k-5 =
            8*(k-2)^7+160*(k-2)^6+1328*(k-2)^5+5932*(k-2)^4+
            15404*(k-2)^3+23269*(k-2)^2+18968*(k-2)+6455 := by ring
        rw [hp]
        have : 0 ≤ k-2 := by linarith
        apply neg_nonpos.mpr
        positivity
      · have : 0 ≤ k^2+k-1 := by nlinarith only [hk',sq_nonneg k]
        have : 0 ≤ 2*k^2+3*k-1 := by nlinarith only [hk',sq_nonneg k]
        positivity
  have lanti (e : ℕ) (he : e ≤ 1) :
      AntitoneOn (fun k => L (N e k) k) (Set.Ici 3) := by
    intro x hx y hy hxy
    change 3 ≤ x at hx
    change 3 ≤ y at hy
    have hn : N e x ≤ N e y := by dsimp [N]; nlinarith only [hx,hy,hxy]
    have hxN := npos e he x hx
    have hyN := npos e he y hy
    have hc := canti e he hx hy hxy
    have hr := one_div_le_one_div_of_le (by linarith : 0 < 6*N e x)
      (by linarith : 6*N e x ≤ 6*N e y)
    have hs := one_div_le_one_div_of_le (by linarith : 0 < 6*(N e x-1))
      (by linarith : 6*(N e x-1) ≤ 6*(N e y-1))
    dsimp [L,C] at hc ⊢
    linarith only [hc,hr,hs]
  have lbase (n k c r : ℝ) (hn : 1 < n) (hk : 0 ≤ k)
      (hc : c = (4*n*(k+1)/(n+k))^2/(n-1))
      (hr : r = 2*k^2/n-1/(3*n)-1/(3*(n-1)))
      (hcert : c < Real.pi*Real.exp r) : L n k < 0 := by
    have hn0 : 0 < n := by linarith
    have hm : 0 < n-1 := by linarith
    have hnk : 0 < n+k := by linarith
    have hk1 : 0 < k+1 := by linarith
    have hc0 : 0 < c := by rw [hc]; positivity
    have hh := Real.log_lt_log hc0 hcert
    rw [Real.log_mul Real.pi_pos.ne' (Real.exp_pos r).ne',Real.log_exp] at hh
    rw [hc,Real.log_div (by positivity) hm.ne', Real.log_pow,
      Real.log_div (by positivity) hnk.ne', Real.log_mul (by positivity) hk1.ne',
      Real.log_mul (by norm_num) hn0.ne'] at hh
    rw [hr] at hh
    dsimp [L]
    have hrem1 : 1/(3*n)=2*(1/(6*n)) := by ring
    have hrem2 : 1/(3*(n-1))=2*(1/(6*(n-1))) := by field_simp; norm_num
    rw [hrem1,hrem2] at hh
    norm_num only [Nat.cast_ofNat] at hh
    rw [show 2*k^2/n = 2*(k^2/n) by ring] at hh
    linarith only [hh]
  have evenbase : L 544 16 < 0 := by
    apply lbase 544 16 (5345344/665175) (832961/886176)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he := Real.sum_le_exp_of_nonneg (x := (832961 : ℝ)/886176) (by positivity) 7
    norm_num [Finset.sum_range_succ,Nat.factorial] at he
    have hp := mul_lt_mul_of_pos_right Real.pi_gt_d2 (Real.exp_pos ((832961 : ℝ)/886176))
    nlinarith only [he,hp]
  have oddbase : L 611 17 < 0 := by
    apply lbase 611 17 (60478002/7517945) (352173/372710)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he := Real.sum_le_exp_of_nonneg (x := (352173 : ℝ)/372710) (by positivity) 5
    norm_num [Finset.sum_range_succ,Nat.factorial] at he
    have hp := mul_lt_mul_of_pos_right Real.pi_gt_d2 (Real.exp_pos ((352173 : ℝ)/372710))
    nlinarith only [he,hp]
  intro n a k e ha hk hodd he hkn hpeak
  have han : 2*a < n := by omega
  have hl := envelope n a ha han
  have hsub : (n : ℝ)-2*a = k := by
    have hh := congrArg (fun z : ℕ => (z : ℝ)) hkn
    push_cast at hh
    linarith only [hh]
  have hN : (n : ℝ) = N e k := by
    have hh := congrArg (fun z : ℕ => (z : ℝ)) hpeak
    push_cast at hh
    dsimp [N]
    linarith only [hh]
  rw [hsub,hN] at hl
  have hL : L (N e k) k < 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with he0 | he1
    · rw [he0]
      have hkk : (16 : ℝ) ≤ k := by exact_mod_cast hk
      have hm := lanti 0 (by norm_num) (by norm_num : (16 : ℝ) ∈ Set.Ici 3)
        (by change (3 : ℝ) ≤ k; linarith only [hkk]) hkk
      exact hm.trans_lt (by convert! evenbase using 1 <;> norm_num [N])
    · rw [he1]
      have hkk : (17 : ℝ) ≤ k := by exact_mod_cast hodd he1
      have hm := lanti 1 (by norm_num) (by norm_num : (17 : ℝ) ∈ Set.Ici 3)
        (by change (3 : ℝ) ≤ k; linarith only [hkk]) hkk
      exact hm.trans_lt (by convert! oddbase using 1 <;> norm_num [N])
  have hh := (Real.log_lt_iff_lt_exp (tpos n a ha han)).mp (hl.trans_lt hL)
  simpa only [Real.exp_zero] using hh

/-- The stronger sufficient arithmetic assertion associated with Conjecture 7.4 of
Gil–Liang–Odetola–Weiner, arXiv:2609.01562v1. The published reduction from grid traffic
to this assertion is a literature input and is not formalized in this module. -/
def claim : Prop := ∀ n a : ℕ, 496 ≤ n → 1 ≤ a → 2*a < n →
  (n : ℚ)*((n-2*a+1 : ℕ) : ℚ)/((n-a : ℕ) : ℚ)*(Nat.choose n a : ℚ)*
    (Nat.choose (n-2) (a-1) : ℚ)/(Nat.choose (2*n-2) (n-1) : ℚ) < 1

/-- The strict rational inequality holds on the entire interior half-domain. -/
theorem result : claim := by
  let T : ℕ → ℕ → ℝ := fun n a =>
    (a : ℝ)*((n : ℝ)-2*a+1)/((n : ℝ)-1) * (Nat.choose n a : ℝ)^2 /
      (Nat.choose (2*n-2) (n-1) : ℝ)
  have tnonneg (n a : ℕ) (han : 2*a < n) : 0 ≤ T n a := by
    have han' : (2 : ℝ)*a < n := by exact_mod_cast han
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have h1 : 0 ≤ (n : ℝ)-2*a+1 := by linarith only [han']
    have h2 : 0 ≤ (n : ℝ)-1 := by linarith only [hn']
    dsimp [T]; positivity
  have cstep (n a : ℕ) (ha : a ≤ n) :
      (Nat.choose (n+2) (a+1) : ℝ) =
        ((n : ℝ)+2)*((n : ℝ)+1)*(Nat.choose n a : ℝ)/
          (((a : ℝ)+1)*((n : ℝ)+1-a)) := by
    have h1 := congrArg (fun z : ℕ => (z : ℝ)) (Nat.add_one_mul_choose_eq (n+1) a)
    have h2 := congrArg (fun z : ℕ => (z : ℝ)) (Nat.choose_mul_succ_eq n a)
    push_cast [Nat.cast_sub (by omega : a ≤ n+1)] at h1 h2
    norm_num only [Nat.add_assoc,Nat.reduceAdd] at h1
    have han : (a : ℝ) ≤ n := by exact_mod_cast ha
    have hd : (0 : ℝ) < n+1-a := by linarith
    apply (eq_div_iff (by positivity)).mpr
    linear_combination -((n : ℝ)+1-a)*h1 - ((n : ℝ)+2)*h2
  have tstep (n a : ℕ) (ha : 1 ≤ a) (han : 2*a < n) :
      T (n+2) (a+1) = T n a *
        (((n : ℝ)*((n : ℝ)-1)*((n : ℝ)+1)^2*((n : ℝ)+2)^2) /
          (4*(a : ℝ)*((a : ℝ)+1)*(2*n-1)*(2*n+1)*((n : ℝ)-a+1)^2)) := by
    have hn : 2 ≤ n := by omega
    have han' : (2 : ℝ)*a < n := by exact_mod_cast han
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hn0 : (0 : ℝ) < n := by linarith
    have hp : (0 : ℝ) < Nat.choose (2*n-2) (n-1) := by
      exact_mod_cast Nat.choose_pos (by omega : n-1 ≤ 2*n-2)
    have hd : (Nat.choose (2*(n+2)-2) (n+2-1) : ℝ) =
        ((2*n+2 : ℝ)*(2*n+1)*(2*n)*(2*n-1)/((n : ℝ)^2*((n : ℝ)+1)^2))*
          (Nat.choose (2*n-2) (n-1) : ℝ) := by
      rw [show 2*(n+2)-2 = (2*n-2)+2+2 by omega,
        show n+2-1 = (n-1)+1+1 by omega,
        cstep _ _ (by omega),cstep _ _ (by omega)]
      push_cast [Nat.cast_sub (by omega : 2 ≤ 2*n),Nat.cast_sub (by omega : 1 ≤ n)]
      field_simp (disch := first | positivity | nlinarith only [hn'])
      <;> ring
    rw [show n+2-1 = n+1 by omega] at hd
    dsimp [T]
    rw [cstep n a (by omega),hd]
    push_cast
    field_simp (disch := first | positivity | nlinarith only [hn',han',ha'])
    <;> ring
  have tdown (n a : ℕ) (ha : 2 ≤ a) (han : 2*a < n) :
      T n (a-1) = T n a *
        (((a : ℝ)-1)*a*((n : ℝ)-2*a+3)/
          (((n : ℝ)-a+1)^2*((n : ℝ)-2*a+1))) := by
    have hn : 2 ≤ n := by omega
    have ha' : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
    have han' : (2 : ℝ)*a < n := by exact_mod_cast han
    have hc : (Nat.choose n (a-1) : ℝ) =
        (Nat.choose n a : ℝ)*a/((n : ℝ)-a+1) := by
      have hh := congrArg (fun z : ℕ => (z : ℝ)) (Nat.choose_succ_right_eq n (a-1))
      rw [Nat.sub_add_cancel (by omega : 1 ≤ a)] at hh
      push_cast [Nat.cast_sub (by omega : a-1 ≤ n),Nat.cast_sub (by omega : 1 ≤ a)] at hh
      apply (eq_div_iff (by linarith : (n : ℝ)-a+1 ≠ 0)).mpr
      linear_combination -hh
    dsimp [T]
    rw [hc]
    push_cast [Nat.cast_sub (by omega : 1 ≤ a)]
    have h1 : 0 < (n : ℝ)-a+1 := by linarith
    have h2 : 0 < (n : ℝ)-2*a+1 := by linarith
    have h3 : 0 < (n : ℝ)-1 := by linarith
    have hp : (0 : ℝ) < Nat.choose (2*n-2) (n-1) := by
      exact_mod_cast Nat.choose_pos (by omega : n-1 ≤ 2*n-2)
    field_simp (disch := first | positivity | linarith only [ha',han'])
    <;> ring
  have lowstep (n a : ℕ) (hn : 496 ≤ n) (ha : 2 ≤ a) (han : 2*a < n)
      (hk : n-2*a ≤ 14) : T n a ≤ T n (a-1) := by
    have hn' : (496 : ℝ) ≤ n := by exact_mod_cast hn
    have ha' : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
    have han' : (2 : ℝ)*a < n := by exact_mod_cast han
    have hk' : (n : ℝ)-2*a ≤ 14 := by
      have hcast : ((n-2*a : ℕ) : ℝ) = (n : ℝ)-2*a := by
        rw [Nat.cast_sub (by omega : 2*a ≤ n)]; push_cast; rfl
      rw [← hcast]; exact_mod_cast hk
    let k : ℝ := (n : ℝ)-2*a
    have k0 : 0 ≤ k := by dsimp [k]; linarith
    have k14 : k ≤ 14 := hk'
    have hf : 2*k^2*n+7*k*n+k-(n : ℝ)^2+5*n+2 ≤ 0 := by
      have hs : k^2 ≤ 14^2 := by nlinarith only [k0,k14]
      have h1 := mul_le_mul_of_nonneg_right hs (show (0 : ℝ) ≤ n by positivity)
      have h2 := mul_le_mul_of_nonneg_right k14 (show (0 : ℝ) ≤ n by positivity)
      nlinarith only [hn',k14,h1,h2,sq_nonneg ((n : ℝ)-496)]
    have hp := tnonneg n a han
    rw [tdown n a ha han]
    apply le_mul_of_one_le_right hp
    have h1 : 0 < (n : ℝ)-a+1 := by linarith
    have h2 : 0 < (n : ℝ)-2*a+1 := by linarith
    apply (one_le_div (by positivity)).mpr
    have hid : ((a : ℝ)-1)*a*((n : ℝ)-2*a+3)-
        (((n : ℝ)-a+1)^2*((n : ℝ)-2*a+1)) =
        -(2*k^2*n+7*k*n+k-(n : ℝ)^2+5*n+2)/2 := by dsimp [k]; ring
    linarith
  let D : ℝ → ℝ → ℝ := fun n k =>
    4*n*(n-1)*(n+1)^2*(n+2)^2 -
      (n-k)*(n-k+2)*(2*n-1)*(2*n+1)*(n+k+2)^2
  let E : ℝ → ℝ → ℝ := fun t x => -4 +
    (8*t^2+36*t+17)/x +
    (32*t^3+304*t^2+916*t+846)/x^2 +
    (44*t^4+600*t^3+3020*t^2+6612*t+5272)/x^3 +
    (24*t^5+428*t^4+3024*t^3+10548*t^2+18096*t+12160)/x^4 +
    (4*t^6+92*t^5+868*t^4+4292*t^3+11704*t^2+16640*t+9600)/x^5
  have decomp (k x : ℝ) (hx : 0 < x) : D (k+x) k / x^5 = E (k-3) x := by
    dsimp [D,E]
    field_simp
    <;> ring
  have eanti (k : ℝ) (hk : 3 ≤ k) : AntitoneOn (E (k-3)) (Set.Ioi 0) := by
    intro x hx y hy hxy
    change 0 < x at hx
    change 0 < y at hy
    have ht : 0 ≤ k-3 := by linarith
    dsimp [E]
    gcongr <;> positivity
  have peaksigns (k : ℝ) (hk : 3 ≤ k) (e : ℕ) (he : e ≤ 1) :
      0 < D (2*k*(k+1)-e-2) k ∧ D (2*k*(k+1)-e) k < 0 := by
    obtain ⟨t, ht, rfl⟩ := exists_nonneg_add_of_le hk
    interval_cases e <;> norm_num only [Nat.cast_zero, Nat.cast_one]
    · constructor
      · have hf : D (2*(3+t)*(3+t+1)-0-2) (3+t) =
            (3+t)^2*(8*t^2+55*t+87)*(8*t^3+88*t^2+307*t+329) := by
          dsimp [D]; ring
        rw [hf]; positivity
      · have hf : D (2*(3+t)*(3+t+1)-0) (3+t) =
            -(3+t)*(128*(3+t)^7+448*(3+t)^6+744*(3+t)^5+776*(3+t)^4+
              563*(3+t)^3+306*(3+t)^2+116*(3+t)+24) := by
          dsimp [D]; ring
        rw [hf]
        have : 0 < (3+t)*(128*(3+t)^7+448*(3+t)^6+744*(3+t)^5+776*(3+t)^4+
              563*(3+t)^3+306*(3+t)^2+116*(3+t)+24) := by positivity
        linarith
    · constructor
      · have hf : D (2*(3+t)*(3+t+1)-1-2) (3+t) =
            (t+2)*(64*t^7+1728*t^6+19656*t^5+121960*t^4+445313*t^3+
              956096*t^2+1117332*t+548400) := by
          dsimp [D]; ring
        rw [hf]; positivity
      · have hf : D (2*(3+t)*(3+t+1)-1) (3+t) =
            -(t+4)^2*(64*t^6+1216*t^5+9560*t^4+39848*t^3+
              92975*t^2+115270*t+59400) := by
          dsimp [D]; ring
        rw [hf]
        have : 0 < (t+4)^2*(64*t^6+1216*t^5+9560*t^4+39848*t^3+
              92975*t^2+115270*t+59400) := by positivity
        linarith
  have dsign (k n : ℝ) (hk : 3 ≤ k) (hn : k+2 ≤ n) (e : ℕ) (he : e ≤ 1) :
      (n ≤ 2*k*(k+1)-e-2 → 0 ≤ D n k) ∧
      (2*k*(k+1)-e ≤ n → D n k ≤ 0) := by
    have he' : (e : ℝ) ≤ 1 := by exact_mod_cast he
    have hn' : 0 < n-k := by linarith
    have hN : 0 < 2*k*(k+1)-e-2-k := by nlinarith
    have hN' : 0 < 2*k*(k+1)-e-k := by linarith
    have hr (m : ℝ) (hm : 0 < m-k) : D m k / (m-k)^5 = E (k-3) (m-k) := by
      convert decomp k (m-k) hm using 1 <;> congr 1 <;> ring
    have hs := peaksigns k hk e he
    constructor
    · intro hb
      have ha := eanti k hk hn' hN (by linarith : n-k ≤ 2*k*(k+1)-e-2-k)
      rw [← hr n hn', ← hr _ hN] at ha
      simpa using (le_div_iff₀ (pow_pos hn' 5)).mp
        (le_trans (le_of_lt (div_pos hs.1 (pow_pos hN 5))) ha)
    · intro hb
      have ha := eanti k hk hN' hn' (by linarith : 2*k*(k+1)-e-k ≤ n-k)
      rw [← hr n hn', ← hr _ hN'] at ha
      simpa using (div_le_iff₀ (pow_pos hn' 5)).mp
        (le_trans ha (le_of_lt (div_neg_of_neg_of_pos hs.2 (pow_pos hN' 5))))
  have stepsign (n a : ℕ) (ha : 1 ≤ a) (han : 2*a < n) :
      (0 ≤ D n ((n : ℝ)-2*a) → T n a ≤ T (n+2) (a+1)) ∧
      (D n ((n : ℝ)-2*a) ≤ 0 → T (n+2) (a+1) ≤ T n a) := by
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have han' : (2 : ℝ)*a < n := by exact_mod_cast han
    have h1 : 0 < (2 : ℝ)*n-1 := by linarith
    have h2 : 0 < (n : ℝ)-a+1 := by linarith
    have hden : 0 < 4*(a : ℝ)*((a : ℝ)+1)*(2*n-1)*(2*n+1)*((n : ℝ)-a+1)^2 := by positivity
    have hid : D n ((n : ℝ)-2*a) = 4*((n : ℝ)*((n : ℝ)-1)*((n : ℝ)+1)^2*((n : ℝ)+2)^2 -
        4*(a : ℝ)*((a : ℝ)+1)*(2*n-1)*(2*n+1)*((n : ℝ)-a+1)^2) := by dsimp [D]; ring
    rw [tstep n a ha han]
    constructor
    · intro hs
      apply le_mul_of_one_le_right (tnonneg n a han)
      apply (one_le_div hden).mpr
      linarith only [hid,hs]
    · intro hs
      apply mul_le_of_le_one_right (tnonneg n a han)
      apply (div_le_one hden).mpr
      linarith only [hid,hs]
  let U : ℕ → ℕ → ℝ := fun k a => T (2*a+k) a
  have ustep (k a : ℕ) (hk : 3 ≤ k) (ha : 1 ≤ a) :
      (0 ≤ D (2*a+k) k → U k a ≤ U k (a+1)) ∧
      (D (2*a+k) k ≤ 0 → U k (a+1) ≤ U k a) := by
    have hh := stepsign (2*a+k) a ha (by omega)
    have hsub : ((2*a+k : ℕ) : ℝ)-2*a = k := by push_cast; ring
    rw [hsub] at hh
    simpa only [U,show 2*(a+1)+k=2*a+k+2 by omega,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh
  have chain (u : ℕ → ℝ) (i j : ℕ) (hij : i ≤ j)
      (hs : ∀ b, i ≤ b → b < j → u b ≤ u (b+1)) : u i ≤ u j := by
    revert hs
    induction j,hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
      intro hs
      exact (ih (fun b hb hb' => hs b hb (by omega))).trans (hs j hij (by omega))
  have upeak (k p a e : ℕ) (hk : 3 ≤ k) (hp : 1 ≤ p) (ha : 1 ≤ a)
      (he : e ≤ 1) (hpeak : 2*p+k+e = 2*k*(k+1)) : U k a ≤ U k p := by
    have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hpeak' : (2 : ℝ)*p+k+e = 2*k*(k+1) := by exact_mod_cast hpeak
    rcases le_total a p with hap | hpa
    · apply chain (U k) a p hap
      intro b hab hbp
      apply (ustep k b hk (by omega)).1
      have hb : (b : ℝ)+1 ≤ p := by exact_mod_cast hbp
      have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
      exact (dsign k (2*b+k) hk' (by linarith only [hb']) e he).1 (by linarith only [hpeak',hb])
    · have hdec := chain (fun b => -U k b) p a hpa
        (fun b hpb hba => neg_le_neg <| (ustep k b hk (by omega)).2 <| by
          have hb : (p : ℝ) ≤ b := by exact_mod_cast hpb
          have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
          exact (dsign k (2*b+k) hk' (by linarith only [hb']) e he).2 (by linarith only [hpeak',hb]))
      linarith only [hdec]
  have utail (k p a e : ℕ) (hk : 3 ≤ k) (hp : 1 ≤ p) (hpa : p ≤ a)
      (he : e ≤ 1) (hpeak : 2*k*(k+1) ≤ 2*p+k+e) : U k a ≤ U k p := by
    have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hpeak' : (2 : ℝ)*k*(k+1) ≤ 2*p+k+e := by exact_mod_cast hpeak
    have hdec := chain (fun b => -U k b) p a hpa
      (fun b hpb hba => neg_le_neg <| (ustep k b hk (by omega)).2 <| by
        have hb : (p : ℝ) ≤ b := by exact_mod_cast hpb
        have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
        exact (dsign k (2*b+k) hk' (by linarith only [hb']) e he).2 (by linarith only [hpeak',hb]))
    linarith only [hdec]
  have reduction (n a : ℕ) (hn : 496 ≤ n) (ha : 1 ≤ a) (han : 2*a < n) :
      ∃ b, 1 ≤ b ∧ 2*b < n ∧ 15 ≤ n-2*b ∧ T n a ≤ T n b := by
    induction a using Nat.strong_induction_on with
    | h a ih =>
      by_cases hk : 15 ≤ n-2*a
      · exact ⟨a,ha,han,hk,le_rfl⟩
      have ha2 : 2 ≤ a := by omega
      obtain ⟨b,hb,hbn,hbk,ht⟩ := ih (a-1) (by omega) (by omega) (by omega)
      exact ⟨b,hb,hbn,hbk,(lowstep n a hn ha2 han (by omega)).trans ht⟩
  have k15base : T 497 241 < 1 := by
    have hc : 241*(Nat.choose 497 241)^2 < 31*Nat.choose 992 496 := by
      rw [Nat.choose_eq_factorial_div_factorial (show 241 ≤ 497 by norm_num),
        Nat.choose_eq_factorial_div_factorial (show 496 ≤ 992 by norm_num)]
      norm_num
    have hc' : (241 : ℝ)*(Nat.choose 497 241 : ℝ)^2 < 31*(Nat.choose 992 496 : ℝ) := by
      exact_mod_cast hc
    have hp : (0 : ℝ) < Nat.choose 992 496 := by
      exact_mod_cast Nat.choose_pos (by norm_num : 496 ≤ 992)
    change ((241 : ℝ)*(497-2*241+1)/(497-1))*(Nat.choose 497 241 : ℝ)^2 /
      (Nat.choose 992 496 : ℝ) < 1
    rw [show (241 : ℝ)*(497-2*241+1)/(497-1) = 241/31 by norm_num]
    apply (div_lt_one hp).mpr
    nlinarith only [hc']
  intro n a hn ha han
  obtain ⟨b,hb,hbn,hbk,hab⟩ := reduction n a hn ha han
  let k := n-2*b
  have hk : 15 ≤ k := hbk
  have hnb : 2*b+k = n := by dsimp [k]; omega
  have hbound : T n b < 1 := by
    by_cases hk15 : k = 15
    · have hnb15 : 2*b+15 = n := by omega
      have hh := utail 15 241 b 1 (by norm_num) (by norm_num) (by omega)
        (by norm_num) (by norm_num)
      rw [← hnb15]
      exact hh.trans_lt k15base
    have hk16 : 16 ≤ k := by omega
    let e := k % 2
    have he : e ≤ 1 := by dsimp [e]; omega
    have hev : 2*((k+e)/2) = k+e := by dsimp [e]; omega
    let p := k*(k+1)-(k+e)/2
    have hm : k+e+2 ≤ 2*(k*(k+1)) := by nlinarith only [hk16,he]
    have hp : 1 ≤ p := by dsimp [p]; omega
    have hpeak : 2*p+k+e = 2*k*(k+1) := by
      calc
        _ = 2*(k*(k+1)) := by dsimp [p]; omega
        _ = _ := by ring
    have hh := upeak k p b e (by omega) hp hb he hpeak
    have hpT := uniform_peak_bound (2*p+k) p k e hp hk16
      (fun he1 => by dsimp [e] at he1; omega) he rfl hpeak
    rw [← hnb]
    exact hh.trans_lt hpT
  have ht := hab.trans_lt hbound
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have han' : (2 : ℝ)*a < n := by exact_mod_cast han
  have hna : 0 < (n : ℝ)-a := by linarith only [ha',han']
  have hnm : 0 < (n : ℝ)-1 := by linarith only [hn']
  have hn0 : (0 : ℝ) < n := by linarith only [hn']
  have hp : (0 : ℝ) < Nat.choose (2*n-2) (n-1) := by
    exact_mod_cast Nat.choose_pos (by omega : n-1 ≤ 2*n-2)
  have hsmall : (Nat.choose (n-2) (a-1) : ℝ) =
      (Nat.choose n a : ℝ)*a*((n : ℝ)-a)/((n : ℝ)*((n : ℝ)-1)) := by
    have h1 := congrArg (fun z : ℕ => (z : ℝ)) (Nat.add_one_mul_choose_eq (n-2) (a-1))
    have h2 := congrArg (fun z : ℕ => (z : ℝ)) (Nat.choose_mul_succ_eq (n-1) a)
    rw [show n-2+1=n-1 by omega,Nat.sub_add_cancel ha] at h1
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h2
    push_cast [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub (by omega : a ≤ n)] at h1 h2
    apply (eq_div_iff (by positivity)).mpr
    linear_combination (n : ℝ)*h1 + (a : ℝ)*h2
  have heq : (n : ℝ)*((n-2*a+1 : ℕ) : ℝ)/((n-a : ℕ) : ℝ)*(Nat.choose n a : ℝ)*
      (Nat.choose (n-2) (a-1) : ℝ)/(Nat.choose (2*n-2) (n-1) : ℝ) = T n a := by
    rw [hsmall]
    push_cast [Nat.cast_sub (by omega : 2*a ≤ n),Nat.cast_sub (by omega : a ≤ n)]
    dsimp [T]
    field_simp (disch := positivity)
    <;> ring
  rw [← heq] at ht
  apply (Rat.cast_lt (K := ℝ)).mp
  push_cast
  simpa only [Nat.cast_add,Nat.cast_one] using ht

end D5.S3.Arith.FactorialRatio.GridAntidiagonalTrafficBound
