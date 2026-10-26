/- GID: D5/S3/Weil/ZetaBridge/ActualNodalTailEnclosure
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualNodalTailEnclosure
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: Actual nodal paired-column infinite upper and lower bounds with a cutoff uniform over all complex vectors. -/

import D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
import D5.S3.Weil.ZetaBridge.ActualNodalCoercivity
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

noncomputable section
open Polynomial MeasureTheory Set
open scoped BigOperators Interval
namespace D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open D5.S3.Weil.ZetaBridge.ActualReciprocalEnclosure
open D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
open D5.S3.Analytic.PolynomialReciprocalBounds

/-- Both nodal denominator comparisons, uniform in all exterior integer modes. -/
private lemma nodal_denominator_bounds (S : Finset ℤ) {N : ℕ} (hN : 0 < N)
    {B : ℝ} (hB : 0 ≤ B) (hBN : 2*B ≤ N)
    (hS : ∀ n ∈ S, |(n:ℝ)| ≤ B) {m : ℤ} (hm : (N:ℝ) < |(m:ℝ)|) :
    (1-B/(N:ℝ))^S.card*|(m:ℝ)|^S.card ≤ ‖(ActualNodalCoercivity.D S).eval (m:ℂ)‖ ∧
    ‖(ActualNodalCoercivity.D S).eval (m:ℂ)‖ ≤ (1+B/(N:ℝ))^S.card*|(m:ℝ)|^S.card := by
  classical
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hr : B/(N:ℝ) < 1 := (div_lt_one hn).2 (by linarith)
  have hma : 0 < |(m:ℝ)| := hn.trans hm
  have hdist (n : ℤ) (hnS : n ∈ S) :
      (1-B/(N:ℝ))*|(m:ℝ)| ≤ ‖(m:ℂ)-(n:ℂ)‖ ∧
      ‖(m:ℂ)-(n:ℂ)‖ ≤ (1+B/(N:ℝ))*|(m:ℝ)| := by
    have hBscale : B ≤ B/(N:ℝ)*|(m:ℝ)| := by
      have h := mul_le_mul_of_nonneg_left hm.le (div_nonneg hB hn.le)
      simpa only [div_mul_cancel₀ _ hn.ne'] using h
    have hnormM : ‖(m:ℂ)‖ = |(m:ℝ)| := Complex.norm_intCast m
    have hnormN : ‖(n:ℂ)‖ = |(n:ℝ)| := Complex.norm_intCast n
    have hlo := norm_sub_norm_le (m:ℂ) (n:ℂ)
    have hhi := norm_sub_le (m:ℂ) (n:ℂ)
    rw [hnormM,hnormN] at hlo hhi
    constructor <;> nlinarith [hS n hnS]
  have he : ‖(ActualNodalCoercivity.D S).eval (m:ℂ)‖ = ∏ n ∈ S, ‖(m:ℂ)-(n:ℂ)‖ := by
    simp only [ActualNodalCoercivity.D, Lagrange.nodal, eval_prod, eval_sub, eval_X, eval_C, norm_prod]
  rw [he]
  constructor
  · have h := Finset.prod_le_prod₀ (s := S)
      (f := fun _ : ℤ => (1-B/(N:ℝ))*|(m:ℝ)|)
      (g := fun n : ℤ => ‖(m:ℂ)-(n:ℂ)‖)
      (fun _ _ => mul_nonneg (sub_pos.mpr hr).le hma.le)
      (fun n hnS => (hdist n hnS).1)
    simpa only [Finset.prod_const,mul_pow] using h
  · have h := Finset.prod_le_prod₀ (s := S)
      (f := fun n : ℤ => ‖(m:ℂ)-(n:ℂ)‖)
      (g := fun _ : ℤ => (1+B/(N:ℝ))*|(m:ℝ)|)
      (fun _ _ => norm_nonneg _) (fun n hnS => (hdist n hnS).2)
    simpa only [Finset.prod_const,mul_pow] using h

private lemma norm_power_ratio {a b z x : ℝ} {d : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hz : 0 ≤ z) (hx : 0 ≤ x) (hd : 1 ≤ d)
    (h : x*b^2 = a^(2*(d-1))*z) {L H : ℝ} (hL : 0 < L) (hH : 0 < H)
    (hlo : L^d*a^d ≤ b) (hhi : b ≤ H^d*a^d) :
    z/(H^(2*d)*a^2) ≤ x ∧ x ≤ z/(L^(2*d)*a^2) := by
  have hpow : a^(2*d) = a^(2*(d-1))*a^2 := by
    rw [← pow_add]
    congr 1
    omega
  have hHpow : (H^d*a^d)^2 = H^(2*d)*a^(2*d) := by
    simp only [mul_pow, ← pow_mul, Nat.mul_comm d 2]
  have hLpow : (L^d*a^d)^2 = L^(2*d)*a^(2*d) := by
    simp only [mul_pow, ← pow_mul, Nat.mul_comm d 2]
  have hi : b^2 ≤ H^(2*d)*a^(2*d) := by
    rw [← hHpow]
    exact pow_le_pow_left₀ hb.le hhi 2
  have hl : L^(2*d)*a^(2*d) ≤ b^2 := by
    rw [← hLpow]
    exact pow_le_pow_left₀ (by positivity) hlo 2
  have hapos : 0 < a^(2*(d-1)) := by positivity
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < H^(2*d)*a^2)).2
    have hmul := mul_le_mul_of_nonneg_left hi hx
    rw [h,hpow] at hmul
    apply le_of_mul_le_mul_left _ hapos
    nlinarith only [hmul]
  · apply (le_div_iff₀ (by positivity : 0 < L^(2*d)*a^2)).2
    have hmul := mul_le_mul_of_nonneg_left hl hx
    rw [h,hpow] at hmul
    apply le_of_mul_le_mul_left _ hapos
    nlinarith only [hmul]

/-- A single actual exterior column, with exact reciprocal polynomial numerators. -/
private lemma actual_column_bounds {c N : ℕ} (S : Finset ℤ) (hSne : S.Nonempty) (v : ℤ → ℂ)
    (hN : 0 < N) {B : ℝ} (hB : 0 ≤ B) (hBN : 2*B ≤ N)
    (hS : ∀ n ∈ S, |(n:ℝ)| ≤ B) {m : ℤ} (hm : (N:ℝ) < |(m:ℝ)|) :
    let d := S.card
    let A := reciprocalPolynomial d N (ActualNodalCoercivity.P c S v)
    let Q := reciprocalPolynomial d N (ActualNodalCoercivity.Q S v)
    let Z := ‖value A ((N:ℝ)/(m:ℝ))-(arithmeticBoundarySymbol c m:ℂ)*value Q ((N:ℝ)/(m:ℝ))‖^2/(m:ℝ)^2
    Z/(Real.pi^2*(1+B/(N:ℝ))^(2*d)) ≤ ‖couplingColumn c S v m‖^2 ∧
    ‖couplingColumn c S v m‖^2 ≤ Z/(Real.pi^2*(1-B/(N:ℝ))^(2*d)) := by
  dsimp only
  have hd : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hma : 0 < |(m:ℝ)| := hn.trans hm
  have hm0 : m ≠ 0 := by intro h; subst m; simpa using hma
  have hmC : (m:ℂ) ≠ 0 := by exact_mod_cast hm0
  have hnot : m ∉ S := by
    intro hmem
    have hb := hS m hmem
    linarith
  have hmodel := ActualNodalCoercivity.actual_nodal_polynomial_model c S hSne v
  let A := reciprocalPolynomial S.card N (ActualNodalCoercivity.P c S v)
  let Q := reciprocalPolynomial S.card N (ActualNodalCoercivity.Q S v)
  have hp := reciprocalPolynomial_exact hd hN (ActualNodalCoercivity.P c S v) hmodel.1 (m:ℂ) hmC
  have hq := reciprocalPolynomial_exact hd hN (ActualNodalCoercivity.Q S v) hmodel.2.1 (m:ℂ) hmC
  have hid := hmodel.2.2 m hnot
  have harg : ((N:ℂ)/(m:ℂ)) = (((N:ℝ)/(m:ℝ):ℝ):ℂ) := by push_cast; rfl
  rw [← hp,← hq,harg] at hid
  have hnumeq : (Real.pi:ℂ)*(ActualNodalCoercivity.D S).eval (m:ℂ)*couplingColumn c S v m =
      (m:ℂ)^(S.card-1)*(value A ((N:ℝ)/(m:ℝ))-
        (arithmeticBoundarySymbol c m:ℂ)*value Q ((N:ℝ)/(m:ℝ))) := by
    convert hid using 1 <;> dsimp [A,Q,value] <;> ring
  have hnorm := congrArg (fun z : ℂ => ‖z‖^2) hnumeq
  simp only [norm_mul,norm_pow,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,← pow_mul] at hnorm
  have hmnorm : ‖(m:ℂ)‖ = |(m:ℝ)| := Complex.norm_intCast m
  rw [hmnorm,Nat.mul_comm (S.card-1) 2] at hnorm
  have hden := nodal_denominator_bounds S hN hB hBN hS hm
  have hLm : 0 < 1-B/(N:ℝ) := sub_pos.mpr ((div_lt_one hn).2 (by linarith))
  have hHp : 0 < 1+B/(N:ℝ) := by positivity
  have hDp : 0 < ‖(ActualNodalCoercivity.D S).eval (m:ℂ)‖ := lt_of_lt_of_le (by positivity) hden.1
  have he : (Real.pi^2*‖couplingColumn c S v m‖^2)*‖(ActualNodalCoercivity.D S).eval (m:ℂ)‖^2 =
      |(m:ℝ)|^(2*(S.card-1))*
        ‖value A ((N:ℝ)/(m:ℝ))-(arithmeticBoundarySymbol c m:ℂ)*value Q ((N:ℝ)/(m:ℝ))‖^2 := by
    convert hnorm using 1 <;> ring
  have hb := norm_power_ratio hma hDp (sq_nonneg _) (by positivity) hd he hLm hHp hden.1 hden.2
  have hpip : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hmr : (m:ℝ) ≠ 0 := by exact_mod_cast hm0
  constructor
  · have hh := div_le_div_of_nonneg_right hb.1 hpip.le
    simp only [sq_abs] at hh
    convert hh using 1 <;> (try dsimp [A,Q,value]) <;>
      field_simp [Real.pi_pos.ne',hmr,hLm.ne',hHp.ne'] <;> ring
  · have hh := div_le_div_of_nonneg_right hb.2 hpip.le
    simp only [sq_abs] at hh
    convert hh using 1 <;> (try dsimp [A,Q,value]) <;>
      field_simp [Real.pi_pos.ne',hmr,hLm.ne',hHp.ne'] <;> ring

end D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure

namespace D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open D5.S3.Weil.ZetaBridge.ActualReciprocalEnclosure
open D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
open D5.S3.Analytic.PolynomialReciprocalBounds

def pairedColumnTerm (c N : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (j : ℕ) : ℝ :=
  ‖couplingColumn c S v ((N+j+1:ℕ):ℤ)‖^2+
    ‖couplingColumn c S v (-((N+j+1:ℕ):ℤ))‖^2

/-- Full paired actual column enclosure (7.3). No coefficient metric appears. -/
theorem actual_paired_column_enclosure {c N : ℕ} (hc : 3 ≤ c)
    (S : Finset ℤ) (hSne : S.Nonempty) (v : ℤ → ℂ)
    (hNdim : S.card^2 ≤ N) {B : ℝ} (hB : 0 ≤ B) (hBN : 2*B ≤ N)
    (hS : ∀ n ∈ S, |(n:ℝ)| ≤ B) :
    let d := S.card
    let A := reciprocalPolynomial d N (ActualNodalCoercivity.P c S v)
    let Q := reciprocalPolynomial d N (ActualNodalCoercivity.Q S v)
    let H := pairedEnergy c A Q
    let ε := (d:ℝ)^2*U c/(N:ℝ)
    Summable (pairedColumnTerm c N S v) ∧
    (1-ε)*H/(Real.pi^2*(N:ℝ)*(1+B/(N:ℝ))^(2*d)) ≤
      (∑' j : ℕ,pairedColumnTerm c N S v j) ∧
    (∑' j : ℕ,pairedColumnTerm c N S v j) ≤
      (1+ε)*H/(Real.pi^2*(N:ℝ)*(1-B/(N:ℝ))^(2*d)) := by
  dsimp only
  have hd : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hdp : 0 < S.card := hd
  have hN : 0 < N := lt_of_lt_of_le (pow_pos hdp 2) hNdim
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  let A := reciprocalPolynomial S.card N (ActualNodalCoercivity.P c S v)
  let Q := reciprocalPolynomial S.card N (ActualNodalCoercivity.Q S v)
  let lo : ℝ := 1/(Real.pi^2*(1+B/(N:ℝ))^(2*S.card))
  let hi : ℝ := 1/(Real.pi^2*(1-B/(N:ℝ))^(2*S.card))
  have hL : 0 < 1-B/(N:ℝ) := sub_pos.mpr ((div_lt_one hn).2 (by linarith))
  have hlo : 0 ≤ lo := by dsimp [lo]; positivity
  have hhi : 0 ≤ hi := by dsimp [hi]; positivity
  have hpair := actual_paired_symbol_enclosure hc hd hNdim A Q
    (reciprocalPolynomial_degree hd _) (reciprocalPolynomial_degree hd _)
  have hpoint (j : ℕ) : lo*pairedTerm c N A Q j ≤ pairedColumnTerm c N S v j ∧
      pairedColumnTerm c N S v j ≤ hi*pairedTerm c N A Q j := by
    have hm : (N:ℝ) < |(((N+j+1:ℕ):ℤ):ℝ)| := by
      simp only [Int.cast_natCast,abs_of_nonneg (show (0:ℝ) ≤ ((N+j+1:ℕ):ℝ) by positivity)]
      exact_mod_cast (show N < N+j+1 by omega)
    have hp := actual_column_bounds (c := c) S hSne v hN hB hBN hS hm
    have hmB := actual_column_bounds (c := c) (m := -((N+j+1:ℕ):ℤ))
      S hSne v hN hB hBN hS (by simpa only [Int.cast_neg, abs_neg] using hm)
    constructor
    · have hh := add_le_add hp.1 hmB.1
      convert hh using 1 <;> dsimp [lo,pairedColumnTerm,pairedTerm,A,Q] <;>
        simp only [Int.cast_neg,Int.cast_natCast,Int.cast_add,Int.cast_one,Nat.cast_add,Nat.cast_one,div_neg,neg_sq] <;> ring
    · have hh := add_le_add hp.2 hmB.2
      convert hh using 1 <;> dsimp [hi,pairedColumnTerm,pairedTerm,A,Q] <;>
        simp only [Int.cast_neg,Int.cast_natCast,Int.cast_add,Int.cast_one,Nat.cast_add,Nat.cast_one,div_neg,neg_sq] <;> ring
  have hnon (j : ℕ) : 0 ≤ pairedColumnTerm c N S v j := by
    unfold pairedColumnTerm
    positivity
  have hsum : Summable (pairedColumnTerm c N S v) :=
    (hpair.1.mul_left hi).of_norm_bounded (fun j => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hnon j)]
      exact (hpoint j).2)
  have hsumlo : lo*(∑' j : ℕ,pairedTerm c N A Q j) ≤ ∑' j : ℕ,pairedColumnTerm c N S v j := by
    rw [← hpair.1.tsum_mul_left lo]
    exact (hpair.1.mul_left lo).tsum_le_tsum (fun j => (hpoint j).1) hsum
  have hsumhi : (∑' j : ℕ,pairedColumnTerm c N S v j) ≤ hi*(∑' j : ℕ,pairedTerm c N A Q j) := by
    rw [← hpair.1.tsum_mul_left hi]
    exact hsum.tsum_le_tsum (fun j => (hpoint j).2) (hpair.1.mul_left hi)
  obtain ⟨hpl,hpu⟩ := abs_le.mp hpair.2
  have hl : (1-(S.card:ℝ)^2*U c/(N:ℝ))*pairedEnergy c A Q/(N:ℝ) ≤
      ∑' j : ℕ,pairedTerm c N A Q j := by
    apply (div_le_iff₀ hn).2
    nlinarith only [hpl]
  have hu : (∑' j : ℕ,pairedTerm c N A Q j) ≤
      (1+(S.card:ℝ)^2*U c/(N:ℝ))*pairedEnergy c A Q/(N:ℝ) := by
    apply (le_div_iff₀ hn).2
    nlinarith only [hpu]
  refine ⟨hsum,?_,?_⟩
  · have hh := (mul_le_mul_of_nonneg_left hl hlo).trans hsumlo
    convert hh using 1 <;> dsimp [lo,A,Q] <;> ring
  · have hh := hsumhi.trans (mul_le_mul_of_nonneg_left hu hhi)
    convert hh using 1 <;> dsimp [hi,A,Q] <;> ring

/-- A single cutoff works for every complex coefficient vector. It uses the
current (possibly large) U; it does not assert the separate explicit336 bound. -/
theorem actual_paired_column_uniform_enclosure {c : ℕ} (hc : 3 ≤ c)
    (S : Finset ℤ) (hSne : S.Nonempty) {B : ℝ} (hB : 0 ≤ B)
    (hS : ∀ n ∈ S, |(n:ℝ)| ≤ B) {η : ℝ} (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ v : ℤ → ℂ, ∀ N : ℕ, N0 ≤ N →
      let d := S.card
      let A := reciprocalPolynomial d N (ActualNodalCoercivity.P c S v)
      let Q := reciprocalPolynomial d N (ActualNodalCoercivity.Q S v)
      let H := pairedEnergy c A Q
      Summable (pairedColumnTerm c N S v) ∧
      (1-η)*H/(Real.pi^2*(N:ℝ)*(1+B/(N:ℝ))^(2*d)) ≤
        (∑' j : ℕ, pairedColumnTerm c N S v j) ∧
      (∑' j : ℕ, pairedColumnTerm c N S v j) ≤
        (1+η)*H/(Real.pi^2*(N:ℝ)*(1-B/(N:ℝ))^(2*d)) := by
  obtain ⟨kB, hkB⟩ := exists_nat_ge (2*B)
  obtain ⟨kE, hkE⟩ := exists_nat_ge ((S.card:ℝ)^2*U c/η)
  let N0 := max 1 (max (S.card^2) (max kB kE))
  refine ⟨N0, ?_⟩
  intro v N hcut
  dsimp only
  have hN : 0 < N := by dsimp [N0] at hcut; omega
  have hdN : S.card^2 ≤ N := by dsimp [N0] at hcut; omega
  have hkBN : kB ≤ N := by dsimp [N0] at hcut; omega
  have hkEN : kE ≤ N := by dsimp [N0] at hcut; omega
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hBN : 2*B ≤ (N:ℝ) := hkB.trans (by exact_mod_cast hkBN)
  have hε : (S.card:ℝ)^2*U c/(N:ℝ) ≤ η := by
    apply (div_le_iff₀ hn).2
    have hh : (S.card:ℝ)^2*U c/η ≤ (N:ℝ) :=
      hkE.trans (by exact_mod_cast hkEN)
    simpa only [mul_comm] using (div_le_iff₀ hη).1 hh
  let A := reciprocalPolynomial S.card N (ActualNodalCoercivity.P c S v)
  let Q := reciprocalPolynomial S.card N (ActualNodalCoercivity.Q S v)
  have hmean : 0 ≤ PrimeSymbolResonance.mean c :=
    (by positivity : (0:ℝ) ≤ (Real.log (2:ℝ))^2/4).trans
      (PrimeSymbolResonance.prime_symbol_mean_lower_bound hc)
  have hH : 0 ≤ pairedEnergy c A Q := by
    rw [pairedEnergy_integral]
    apply intervalIntegral.integral_nonneg_of_forall (by norm_num)
    intro t
    positivity
  have hL : 0 < 1-B/(N:ℝ) :=
    sub_pos.mpr ((div_lt_one hn).2 (by linarith))
  have henc := actual_paired_column_enclosure hc S hSne v hdN hB hBN hS
  dsimp only at henc
  refine ⟨henc.1, ?_, ?_⟩
  · refine le_trans ?_ henc.2.1
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right hε hH
    dsimp only [A, Q] at hh
    nlinarith only [hh]
  · refine henc.2.2.trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right hε hH
    dsimp only [A, Q] at hh
    nlinarith only [hh]

end D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
