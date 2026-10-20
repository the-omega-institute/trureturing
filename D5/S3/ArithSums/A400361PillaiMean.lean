/- GID: D5/S3/ArithSums/A400361PillaiMean
   generality: G
   mirror-B: D5/B/S3/ArithSums/A400361PillaiMean
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The classical Pillai second term and elementary kernels consumed by the full A400361 proof. -/

import D5.S3.Factorization.AlternatingGcdSumPillai
import D5.S3.Weil.ZetaGamma.GammaSeries
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter Topology Finset
open scoped BigOperators Asymptotics

namespace D5.S3.ArithSums.A400361PillaiMean

/-- The real restriction of the Riemann zeta function. -/
noncomputable def realZeta (x : ℝ) : ℝ := (riemannZeta (x : ℂ)).re

private lemma realZeta_derivative :
    deriv realZeta 2 = (deriv riemannZeta (2 : ℂ)).re := by
  have hd : DifferentiableAt ℂ riemannZeta (2 : ℂ) :=
    differentiableAt_riemannZeta (by norm_num)
  exact hd.hasDerivAt.real_of_complex.deriv

theorem kernel_one_prefix (N : ℕ) :
    (∑ j ∈ range N, 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) =
      1 - 1 / ((N : ℝ) + 1) := by
  calc
    (∑ j ∈ range N, 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) =
        ∑ j ∈ range N, (1 / ((j : ℝ) + 1) - 1 / (((j + 1 : ℕ) : ℝ) + 1)) := by
      apply sum_congr rfl
      intro j hj
      push_cast
      have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      <;> ring
    _ = _ := by
      simpa only [Nat.cast_zero, zero_add, div_one] using
        (Finset.sum_range_sub' (fun j : ℕ => 1 / ((j : ℝ) + 1)) N)

theorem hasSum_kernel_one :
    HasSum (fun j : ℕ => 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j => by positivity) 1).mpr
  simp_rw [kernel_one_prefix]
  have h : Tendsto (fun N : ℕ => 1 / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  simpa only [Nat.cast_add, Nat.cast_one, sub_zero] using tendsto_const_nhds.sub h

theorem sum_Icc_cast (q : ℕ) :
    (∑ r ∈ Icc 1 q, (r : ℝ)) = (q : ℝ) * ((q : ℝ) + 1) / 2 := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (Finset.sum_range_id_mul_two (q + 1))
  simp only [Nat.add_sub_cancel] at h
  push_cast at h
  rw [Finset.sum_range_eq_add_Ico (fun n : ℕ => (n : ℝ)) (by omega : 0 < q + 1),
    Finset.Ico_add_one_right_eq_Icc] at h
  simp only [Nat.cast_zero, zero_add] at h
  linarith

theorem quotient_ratio_limit (d : ℕ) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / N) atTop (𝓝 (1 / (d : ℝ))) := by
  convert (tendsto_nat_floor_mul_div_atTop (show (0 : ℝ) ≤ 1 / (d : ℝ) by positivity)).comp
    tendsto_natCast_atTop_atTop using 1
  funext N
  simp only [Function.comp_apply]
  rw [show (1 / (d : ℝ)) * (N : ℝ) = (N : ℝ) / d by ring, Nat.floor_div_eq_div]

private noncomputable def weightedPairs (N : ℕ) : ℝ :=
  ∑ p ∈ (((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)),
    (p.1 : ℝ) * p.2

private lemma weightedPairs_hyperbola (N : ℕ) :
    weightedPairs N =
      2 * (∑ a ∈ Icc 1 (Nat.sqrt N), (a : ℝ) *
        ∑ b ∈ Icc 1 (N / a), (b : ℝ)) -
          (∑ a ∈ Icc 1 (Nat.sqrt N), (a : ℝ))^2 := by
  classical
  let M := Nat.sqrt N
  let T := (((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N))
  let L := T.filter (fun p => p.1 ≤ M)
  let R := T.filter (fun p => p.2 ≤ M)
  have hM : M ≤ N := Nat.sqrt_le_self N
  have hMsq : M * M ≤ N := Nat.sqrt_le N
  have hMhi : N < (M + 1) * (M + 1) := Nat.lt_succ_sqrt N
  have hunion : L ∪ R = T := by
    ext p
    simp only [L, R, mem_union, mem_filter]
    constructor
    · tauto
    · intro hp
      have hpN := (mem_filter.mp hp).2
      by_cases hpa : p.1 ≤ M
      · exact Or.inl ⟨hp, hpa⟩
      · right
        refine ⟨hp, ?_⟩
        by_contra hpb
        have hlo : (M + 1) * (M + 1) ≤ p.1 * p.2 :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
  have hinter : L ∩ R = (Icc 1 M) ×ˢ (Icc 1 M) := by
    ext p
    simp only [L, R, T, mem_inter, mem_filter, mem_product, mem_Icc]
    constructor
    · tauto
    · rintro ⟨ha, hb⟩
      have hprod := (Nat.mul_le_mul ha.2 hb.2).trans hMsq
      have ht : ((1 ≤ p.1 ∧ p.1 ≤ N) ∧ (1 ≤ p.2 ∧ p.2 ≤ N)) ∧ p.1 * p.2 ≤ N :=
        ⟨⟨⟨ha.1, ha.2.trans hM⟩, ⟨hb.1, hb.2.trans hM⟩⟩, hprod⟩
      exact ⟨⟨ht, ha.2⟩, ⟨ht, hb.2⟩⟩
  have hleft : (∑ p ∈ L, (p.1 : ℝ) * p.2) =
      ∑ a ∈ Icc 1 M, (a : ℝ) * ∑ b ∈ Icc 1 (N / a), (b : ℝ) := by
    have hset : L = ((Icc 1 M) ×ˢ (Icc 1 N)).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N) := by
      ext p
      simp only [L, T, mem_filter, mem_product, mem_Icc]
      constructor
      · tauto
      · rintro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨⟨⟨⟨ha.1, ha.2.trans hM⟩, hb⟩, hab⟩, ha.2⟩
    rw [hset, sum_filter, sum_product]
    apply sum_congr rfl
    intro a ha
    rw [mul_sum, ← sum_filter]
    have he : (Icc 1 N).filter (fun b => a * b ≤ N) = Icc 1 (N / a) := by
      ext b
      simp only [mem_filter, mem_Icc]
      have hap : 0 < a := by have := (mem_Icc.mp ha).1; omega
      constructor
      · rintro ⟨hb, hab⟩
        exact ⟨hb.1, (Nat.le_div_iff_mul_le hap).mpr (by nlinarith)⟩
      · rintro ⟨hb, hab⟩
        exact ⟨⟨hb, hab.trans (Nat.div_le_self N a)⟩,
          by have hh := (Nat.le_div_iff_mul_le hap).mp hab; nlinarith⟩
    rw [he]
  have hright : (∑ p ∈ R, (p.1 : ℝ) * p.2) = ∑ p ∈ L, (p.1 : ℝ) * p.2 := by
    apply sum_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [L, R, T, mem_filter, mem_product, mem_Icc] at hp ⊢
      rcases hp with ⟨⟨⟨ha, hb⟩, hab⟩, hbM⟩
      exact ⟨⟨⟨hb, ha⟩, by nlinarith⟩, hbM⟩
    · intro p hp q hq he
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    · intro p hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      simp only [L, R, T, mem_filter, mem_product, mem_Icc] at hp ⊢
      rcases hp with ⟨⟨⟨ha, hb⟩, hab⟩, haM⟩
      exact ⟨⟨⟨hb, ha⟩, by nlinarith⟩, haM⟩
    · intro p hp
      dsimp
      ring
  have hcross : (∑ p ∈ L ∩ R, (p.1 : ℝ) * p.2) =
      (∑ a ∈ Icc 1 M, (a : ℝ))^2 := by
    rw [hinter, sum_product, pow_two, sum_mul]
    apply sum_congr rfl
    intro a ha
    rw [mul_sum]
  have he := sum_union_inter (s₁ := L) (s₂ := R) (f := fun p => (p.1 : ℝ) * p.2)
  rw [hunion, hcross, hright, hleft] at he
  change weightedPairs N + _ = _ at he
  dsimp [M] at he
  linarith

private lemma triangular_floor_error (N a : ℕ) (ha : 0 < a) :
    ‖(a : ℝ) * (∑ b ∈ Icc 1 (N / a), (b : ℝ)) - (N : ℝ)^2 / (2 * a)‖ ≤ N := by
  rw [sum_Icc_cast, Real.norm_eq_abs]
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hq : (0 : ℝ) ≤ (N / a : ℕ) := Nat.cast_nonneg _
  have hlo : (a : ℝ) * (N / a : ℕ) ≤ N := by exact_mod_cast Nat.mul_div_le N a
  have hhi : (N : ℝ) < (a : ℝ) * (((N / a : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ N ha
  have he : (a : ℝ) * (((N / a : ℕ) : ℝ) * (((N / a : ℕ) : ℝ) + 1) / 2) -
      (N : ℝ)^2 / (2 * a) =
      (((a : ℝ) * (N / a : ℕ))^2 + a * (a * (N / a : ℕ)) - (N : ℝ)^2) / (2 * a) := by
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * a), div_le_iff₀ (by positivity), abs_le]
  have ht : (0 : ℝ) ≤ a * (N / a : ℕ) := by positivity
  have hsq := mul_self_le_mul_self ht hlo
  have hprod := mul_nonneg
    (show (0 : ℝ) ≤ a - ((N : ℝ) - a * (N / a : ℕ)) by linarith)
    (show (0 : ℝ) ≤ N + a * (N / a : ℕ) by positivity)
  have hat := mul_le_mul_of_nonneg_left hlo har.le
  constructor <;> nlinarith

private lemma harmonic_Icc (M : ℕ) :
    (∑ a ∈ Icc 1 M, 1 / (a : ℝ)) = (harmonic M : ℝ) := by
  induction M with
  | zero => simp [harmonic]
  | succ M ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih, harmonic_succ]
    push_cast
    simp only [one_div]

private lemma hyperbola_sum_error (N M : ℕ) :
    ‖(∑ a ∈ Icc 1 M, (a : ℝ) * ∑ b ∈ Icc 1 (N / a), (b : ℝ)) -
      (N : ℝ)^2 / 2 * (harmonic M : ℝ)‖ ≤ (N : ℝ) * M := by
  have he : (∑ a ∈ Icc 1 M, (a : ℝ) * ∑ b ∈ Icc 1 (N / a), (b : ℝ)) -
      (N : ℝ)^2 / 2 * (harmonic M : ℝ) =
      ∑ a ∈ Icc 1 M, ((a : ℝ) * (∑ b ∈ Icc 1 (N / a), (b : ℝ)) -
        (N : ℝ)^2 / (2 * a)) := by
    rw [sum_sub_distrib, ← harmonic_Icc, mul_sum]
    congr 1
    apply sum_congr rfl
    intro a ha
    ring
  rw [he]
  calc
    _ ≤ ∑ a ∈ Icc 1 M, ‖(a : ℝ) * (∑ b ∈ Icc 1 (N / a), (b : ℝ)) -
        (N : ℝ)^2 / (2 * a)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Icc 1 M, (N : ℝ) := by
      apply sum_le_sum
      intro a ha
      exact triangular_floor_error N a (by have := (mem_Icc.mp ha).1; omega)
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

private lemma sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro K
  exact ⟨K * K, fun N hN => Nat.le_sqrt.mpr hN⟩

private lemma sqrt_ratios :
    Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ) / N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ)^2 / N) atTop (𝓝 1) := by
  have hi : Tendsto (fun N : ℕ => 1 / (Nat.sqrt N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp sqrt_atTop
  constructor
  · apply squeeze_zero' _ _ hi
    · exact Eventually.of_forall (fun N => by positivity)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hM : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr (by omega)
      have hMr : (0 : ℝ) < Nat.sqrt N := by positivity
      have hNr : (0 : ℝ) < N := by positivity
      apply (div_le_div_iff₀ hNr hMr).mpr
      simp only [one_mul]
      exact_mod_cast Nat.sqrt_le N
  · have hi' : Tendsto (fun N : ℕ => 1 / ((Nat.sqrt N : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
          ((tendsto_add_atTop_nat 1).comp sqrt_atTop)
    have hq : Tendsto (fun N : ℕ => ((Nat.sqrt N : ℝ) / ((Nat.sqrt N : ℝ) + 1))^2)
        atTop (𝓝 1) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hi').pow 2
      convert h using 1
      · funext N
        congr 1
        field_simp
        <;> ring
      · norm_num
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hq tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNr : (0 : ℝ) < N := by positivity
      rw [div_pow]
      apply div_le_div_of_nonneg_left (sq_nonneg _) hNr
      exact_mod_cast (Nat.lt_succ_sqrt' N).le
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNr : (0 : ℝ) < N := by positivity
      apply (div_le_iff₀ hNr).mpr
      simpa only [one_mul] using (show (Nat.sqrt N : ℝ)^2 ≤ N by exact_mod_cast Nat.sqrt_le' N)

private lemma weightedPairs_second_term :
    Tendsto (fun N : ℕ => weightedPairs N / (N : ℝ)^2 - (1 / 2 : ℝ) * Real.log N)
      atTop (𝓝 (Real.eulerMascheroniConstant - 1 / 4)) := by
  let E : ℕ → ℝ := fun N =>
    (∑ a ∈ Icc 1 (Nat.sqrt N), (a : ℝ) * ∑ b ∈ Icc 1 (N / a), (b : ℝ)) -
      (N : ℝ)^2 / 2 * (harmonic (Nat.sqrt N) : ℝ)
  have hE : Tendsto (fun N : ℕ => E N / (N : ℝ)^2) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ sqrt_ratios.1
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (N : ℝ) ≠ 0 := by positivity
    rw [norm_div, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ((N : ℝ) * Nat.sqrt N) / (N : ℝ)^2 :=
        div_le_div_of_nonneg_right (hyperbola_sum_error N (Nat.sqrt N)) (sq_nonneg _)
      _ = _ := by field_simp
  have hlog : Tendsto (fun N : ℕ => Real.log (Nat.sqrt N) - Real.log N / 2)
      atTop (𝓝 0) := by
    have ht := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      sqrt_ratios.2).div_const 2
    apply Tendsto.congr' (f₁ := fun N : ℕ => Real.log ((Nat.sqrt N : ℝ)^2 / N) / 2) _
      (show Tendsto _ atTop (𝓝 0) by simpa using ht)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hM : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr (by omega)
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
    ring
  have hH := (Real.tendsto_harmonic_sub_log.comp sqrt_atTop).add hlog
  have hJ : Tendsto (fun N : ℕ => (∑ a ∈ Icc 1 (Nat.sqrt N), (a : ℝ)) / N)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have ht := (sqrt_ratios.2.add sqrt_ratios.1).div_const 2
    convert ht using 1
    · funext N
      rw [sum_Icc_cast]
      ring
    · norm_num
  have ht := (hH.add (hE.const_mul 2)).sub (hJ.pow 2)
  apply Tendsto.congr' (f₁ := fun N : ℕ =>
    ((harmonic (Nat.sqrt N) : ℝ) - Real.log (Nat.sqrt N) +
      (Real.log (Nat.sqrt N) - Real.log N / 2) + 2 * (E N / (N : ℝ)^2)) -
        ((∑ a ∈ Icc 1 (Nat.sqrt N), (a : ℝ)) / N)^2) _
    (show Tendsto _ atTop (𝓝 (Real.eulerMascheroniConstant - 1 / 4)) by
      convert ht using 1 <;> norm_num)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (N : ℝ) ≠ 0 := by positivity
  rw [weightedPairs_hyperbola]
  dsimp [E]
  field_simp
  <;> ring

private lemma term_two_real (f : ℕ → ℝ) (n : ℕ) :
    LSeries.term (fun n => (f n : ℂ)) 2 n = ((f n / (n : ℝ)^2 : ℝ) : ℂ) := by
  by_cases hn : n = 0
  · simp [hn]
  · simp [LSeries.term_of_ne_zero hn, Complex.cpow_ofNat]

private lemma log_square_summable :
    Summable (fun j : ℕ => Real.log ((j + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ)^2) := by
  have hc := LSeriesSummable_logMul_of_lt_re (f := 1) (s := 2)
    (by rw [LSeries.abscissaOfAbsConv_one];
        exact_mod_cast (show (1 : ℝ) < (2 : ℂ).re by norm_num))
  have he (n : ℕ) : (LSeries.term (LSeries.logMul 1) 2 n).re = Real.log n / (n : ℝ)^2 := by
    have hf : LSeries.logMul 1 = (fun n : ℕ => ((Real.log n : ℝ) : ℂ)) := by
      funext n
      simp [LSeries.logMul, Complex.natCast_log]
    rw [hf, term_two_real, Complex.ofReal_re]
  have hr := (Complex.hasSum_re hc.hasSum).summable
  simp_rw [he] at hr
  exact (summable_nat_add_iff 1).mpr hr

private noncomputable def mu (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ)

private lemma mu_bound (n : ℕ) : ‖mu n‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  dsimp [mu]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

private lemma mu_square_summable : Summable (fun j : ℕ => mu (j + 1) / ((j + 1 : ℕ) : ℝ)^2) := by
  have hp : Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ)^2) := by
    simpa using (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
  apply hp.of_norm_bounded
  intro j
  rw [norm_div, Real.norm_of_nonneg (sq_nonneg _)]
  exact div_le_div_of_nonneg_right (mu_bound _) (sq_nonneg _)

private lemma mu_log_square_summable :
    Summable (fun j : ℕ => mu (j + 1) * Real.log ((j + 1 : ℕ) : ℝ) /
      ((j + 1 : ℕ) : ℝ)^2) := by
  apply log_square_summable.of_norm_bounded
  intro j
  rw [norm_div, norm_mul, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.log_natCast_nonneg _)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ 1 * Real.log ((j + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (mu_bound _) (Real.log_natCast_nonneg _)
    _ = _ := one_mul _

private lemma zeta_two_real : riemannZeta (2 : ℂ) = ((Real.pi^2 / 6 : ℝ) : ℂ) := by
  have hs : HasSum (fun n : ℕ => ((1 / (n : ℝ)^2 : ℝ) : ℂ))
      ((Real.pi^2 / 6 : ℝ) : ℂ) := Complex.hasSum_ofReal.mpr hasSum_zeta_two
  have ht := LSeriesHasSum_one (s := 2) (by norm_num)
  have hfun : (1 : ℕ → ℂ) = (fun _ => ((1 : ℝ) : ℂ)) := by funext n; simp
  have he : LSeries.term (1 : ℕ → ℂ) 2 = (fun n : ℕ => ((1 / (n : ℝ)^2 : ℝ) : ℂ)) := by
    funext n
    rw [hfun, term_two_real]
  change HasSum (LSeries.term (1 : ℕ → ℂ) 2) (riemannZeta (2 : ℂ)) at ht
  rw [he] at ht
  exact ht.unique hs

private noncomputable def muSeriesZero : ℝ := ∑' n : ℕ, mu n / (n : ℝ)^2

private noncomputable def muSeriesLog : ℝ := ∑' n : ℕ, mu n * Real.log n / (n : ℝ)^2

private lemma mu_series_values :
    muSeriesZero = 6 / Real.pi^2 ∧
      muSeriesLog = 36 * deriv realZeta 2 / Real.pi^4 := by
  let mc : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)
  have hs0 : Summable (fun n : ℕ => mu n / (n : ℝ)^2) :=
    (summable_nat_add_iff 1).mp mu_square_summable
  have hs1 : Summable (fun n : ℕ => mu n * Real.log n / (n : ℝ)^2) :=
    (summable_nat_add_iff 1).mp mu_log_square_summable
  have hf0 : mc = (fun n => (mu n : ℂ)) := by
    funext n
    simp [mc, mu]
  have hf1 : LSeries.logMul mc = (fun n => ((mu n * Real.log n : ℝ) : ℂ)) := by
    funext n
    simp [LSeries.logMul, mc, mu, Complex.natCast_log, mul_comm]
  have hval0 : LSeries mc 2 = (muSeriesZero : ℂ) := by
    have ht : HasSum (fun n : ℕ => ((mu n / (n : ℝ)^2 : ℝ) : ℂ)) (muSeriesZero : ℂ) :=
      Complex.hasSum_ofReal.mpr hs0.hasSum
    change (∑' n, LSeries.term mc 2 n) = _
    rw [hf0]
    simp_rw [term_two_real]
    exact ht.tsum_eq
  have hval1 : LSeries (LSeries.logMul mc) 2 = (muSeriesLog : ℂ) := by
    have ht : HasSum (fun n : ℕ => ((mu n * Real.log n / (n : ℝ)^2 : ℝ) : ℂ))
        (muSeriesLog : ℂ) := Complex.hasSum_ofReal.mpr hs1.hasSum
    change (∑' n, LSeries.term (LSeries.logMul mc) 2 n) = _
    rw [hf1]
    simp_rw [term_two_real]
    exact ht.tsum_eq
  have hmul := LSeries_one_mul_Lseries_moebius (s := 2) (by norm_num)
  change LSeries 1 2 * LSeries mc 2 = 1 at hmul
  rw [LSeries_one_eq_riemannZeta (by norm_num), zeta_two_real, hval0] at hmul
  have hmulr := congrArg Complex.re hmul
  simp only [← Complex.ofReal_mul, Complex.ofReal_re, Complex.one_re] at hmulr
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hM : muSeriesZero = 6 / Real.pi^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hpi)).mpr
    nlinarith
  refine ⟨hM, ?_⟩
  have hab : LSeries.abscissaOfAbsConv mc < (2 : ℂ).re := by
    change LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.moebius n : ℂ)) < _
    rw [ArithmeticFunction.abscissaOfAbsConv_moebius]
    exact_mod_cast (show (1 : ℝ) < (2 : ℂ).re by norm_num)
  have hd := ((differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).hasDerivAt).mul
    (LSeries_hasDerivAt hab)
  have hev : (fun s : ℂ => riemannZeta s * LSeries mc s) =ᶠ[𝓝 (2 : ℂ)] (fun _ => 1) := by
    have hop : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hop.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with s hs
    rw [← LSeries_one_eq_riemannZeta hs]
    exact LSeries_one_mul_Lseries_moebius hs
  have hc : HasDerivAt (fun s : ℂ => riemannZeta s * LSeries mc s) 0 (2 : ℂ) :=
    (hasDerivAt_const (2 : ℂ) (1 : ℂ)).congr_of_eventuallyEq hev
  have he := hd.unique hc
  rw [hval0, hval1, zeta_two_real] at he
  have her := congrArg Complex.re he
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, mul_zero, zero_mul,
    sub_zero] at her
  rw [hM, ← realZeta_derivative] at her
  apply (eq_div_iff (pow_ne_zero 4 hpi)).mpr
  field_simp at her
  nlinarith [her]

private noncomputable def weightedResidual (N : ℕ) : ℝ :=
  weightedPairs N / (N : ℝ)^2 - (1 / 2 : ℝ) * Real.log N

private lemma weightedResidual_bound : ∃ K : ℝ, 0 < K ∧ ∀ N, ‖weightedResidual N‖ ≤ K := by
  obtain ⟨K, hK, h⟩ := (Metric.isBounded_range_of_tendsto weightedResidual
    weightedPairs_second_term).exists_pos_norm_le
  exact ⟨K, hK, fun N => h _ (Set.mem_range_self N)⟩

private noncomputable def residualMobiusTerm (N d : ℕ) : ℝ :=
  mu d * weightedResidual (N / d) * (((N / d : ℕ) : ℝ) / N)^2

private lemma residualMobius_limit :
    Tendsto (fun N : ℕ => ∑' d : ℕ, residualMobiusTerm N d) atTop
      (𝓝 ((Real.eulerMascheroniConstant - 1 / 4) * muSeriesZero)) := by
  obtain ⟨K, hK, hbound⟩ := weightedResidual_bound
  have hp := hasSum_zeta_two.summable.mul_left K
  have hpoint (d : ℕ) : Tendsto (fun N : ℕ => residualMobiusTerm N d) atTop
      (𝓝 (mu d * (Real.eulerMascheroniConstant - 1 / 4) / (d : ℝ)^2)) := by
    by_cases hd : d = 0
    · simp [residualMobiusTerm, hd, mu]
    · have ht := ((weightedPairs_second_term.comp (Nat.tendsto_div_const_atTop hd)).mul
        ((quotient_ratio_limit d).pow 2)).const_mul (mu d)
      convert ht using 1
      · funext N
        dsimp [residualMobiusTerm, weightedResidual]
        ring
      · congr 1
        ring
  have hdom (N d : ℕ) : ‖residualMobiusTerm N d‖ ≤ K * (1 / (d : ℝ)^2) := by
    by_cases hd : d = 0
    · simp [residualMobiusTerm, hd, mu]
    by_cases hN : N = 0
    · simp [residualMobiusTerm, hN]
      positivity
    have hdr : (0 : ℝ) < d := by positivity
    have hNr : (0 : ℝ) < N := by positivity
    have hratio : ((N / d : ℕ) : ℝ) / N ≤ 1 / (d : ℝ) := by
      apply (div_le_div_iff₀ hNr hdr).mpr
      simp only [one_mul]
      exact_mod_cast Nat.div_mul_le_self N d
    rw [residualMobiusTerm, norm_mul, norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (1 * K) * (1 / (d : ℝ))^2 :=
        mul_le_mul (mul_le_mul (mu_bound d) (hbound _) (norm_nonneg _) (by norm_num))
          (pow_le_pow_left₀ (by positivity) hratio 2) (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have ht := tendsto_tsum_of_dominated_convergence hp hpoint
    (Eventually.of_forall hdom)
  have he : (∑' d : ℕ, mu d * (Real.eulerMascheroniConstant - 1 / 4) / (d : ℝ)^2) =
      (Real.eulerMascheroniConstant - 1 / 4) * muSeriesZero := by
    rw [muSeriesZero, ← tsum_mul_left]
    apply tsum_congr
    intro d
    ring
  rwa [he] at ht

private lemma log_majorant_summable :
    Summable (fun d : ℕ => Real.log (2 * (d : ℝ)) / (d : ℝ)^2) := by
  have h0 := hasSum_zeta_two.summable.mul_left (Real.log 2)
  have h1 : Summable (fun d : ℕ => Real.log d / (d : ℝ)^2) :=
    (summable_nat_add_iff 1).mp log_square_summable
  apply (h0.add h1).congr
  intro d
  by_cases hd : d = 0
  · simp [hd]
  · rw [Real.log_mul (by norm_num) (by positivity)]
    ring

private noncomputable def logarithmicMobiusTerm (N d : ℕ) : ℝ :=
  mu d * (((N / d : ℕ) : ℝ) / N)^2 * Real.log (((N / d : ℕ) : ℝ) / N)

private lemma logarithmicMobius_bound (N d : ℕ) :
    ‖logarithmicMobiusTerm N d‖ ≤ Real.log (2 * (d : ℝ)) / (d : ℝ)^2 := by
  by_cases hd : d = 0
  · simp [logarithmicMobiusTerm, hd, mu]
  have hdr : (0 : ℝ) < d := by positivity
  have hlogd : 0 ≤ Real.log (2 * (d : ℝ)) := by
    apply Real.log_nonneg
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
    linarith
  by_cases hq : N / d = 0
  · simp [logarithmicMobiusTerm, hq]
    exact div_nonneg hlogd (sq_nonneg _)
  have hNr : (0 : ℝ) < N := by
    have hqn : 0 < N / d := Nat.pos_of_ne_zero hq
    have hNp : 0 < N := lt_of_lt_of_le hqn (Nat.div_le_self N d)
    exact_mod_cast hNp
  have hqr : (0 : ℝ) < (N / d : ℕ) := by positivity
  have hratio : ((N / d : ℕ) : ℝ) / N ≤ 1 / (d : ℝ) := by
    apply (div_le_div_iff₀ hNr hdr).mpr
    simp only [one_mul]
    exact_mod_cast Nat.div_mul_le_self N d
  have hrat1 : ((N / d : ℕ) : ℝ) / N ≤ 1 := by
    apply (div_le_one hNr).mpr
    exact_mod_cast Nat.div_le_self N d
  have hlog : Real.log (((N / d : ℕ) : ℝ) / N) ≤ 0 :=
    Real.log_nonpos (by positivity) hrat1
  have hinv : (N : ℝ) / (N / d : ℕ) ≤ 2 * d := by
    apply (div_le_iff₀ hqr).mpr
    have hh : (N : ℝ) < (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ N (by omega : 0 < d)
    have hq1 : (1 : ℝ) ≤ (N / d : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
    nlinarith
  have hlogs : -Real.log (((N / d : ℕ) : ℝ) / N) ≤ Real.log (2 * (d : ℝ)) := by
    have hh := Real.log_le_log (show (0 : ℝ) < (N : ℝ) / (N / d : ℕ) by positivity) hinv
    rw [Real.log_div hNr.ne' hqr.ne'] at hh
    rw [Real.log_div hqr.ne' hNr.ne']
    linarith
  rw [logarithmicMobiusTerm, norm_mul, norm_mul,
    Real.norm_of_nonneg (sq_nonneg _)]
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonpos hlog]
  calc
    _ ≤ (1 * (1 / (d : ℝ))^2) * Real.log (2 * (d : ℝ)) :=
      mul_le_mul (mul_le_mul (mu_bound d) (pow_le_pow_left₀ (by positivity) hratio 2)
          (sq_nonneg _) (by norm_num)) hlogs (by linarith) (by positivity)
    _ = _ := by ring

private lemma logarithmicMobius_limit :
    Tendsto (fun N : ℕ => ∑' d : ℕ, logarithmicMobiusTerm N d) atTop
      (𝓝 (-muSeriesLog)) := by
  have hpoint (d : ℕ) : Tendsto (fun N : ℕ => logarithmicMobiusTerm N d) atTop
      (𝓝 (-mu d * Real.log d / (d : ℝ)^2)) := by
    by_cases hd : d = 0
    · simp [logarithmicMobiusTerm, hd, mu]
    have hq := quotient_ratio_limit d
    have hl := (Real.continuousAt_log (by positivity : (1 / (d : ℝ)) ≠ 0)).tendsto.comp hq
    have ht := ((hq.pow 2).const_mul (mu d)).mul hl
    convert ht using 1
    · rfl
    · congr 1
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one]
      ring
  have ht := tendsto_tsum_of_dominated_convergence log_majorant_summable hpoint
    (Eventually.of_forall logarithmicMobius_bound)
  have he : (∑' d : ℕ, -mu d * Real.log d / (d : ℝ)^2) = -muSeriesLog := by
    rw [muSeriesLog, ← tsum_neg]
    apply tsum_congr
    intro d
    ring
  rwa [he] at ht

private lemma reciprocal_square_tail (N : ℕ) (hN : 0 < N) :
    (∑' j : ℕ, 1 / ((j + N + 1 : ℕ) : ℝ)^2) ≤ 1 / (N : ℝ) := by
  have hs := (hasSum_nat_add_iff' (N - 1)).mpr hasSum_kernel_one
  rw [kernel_one_prefix] at hs
  have hc : HasSum (fun j : ℕ =>
      1 / (((j + N : ℕ) : ℝ) * ((j + N + 1 : ℕ) : ℝ))) (1 / (N : ℝ)) := by
    convert hs using 1
    · funext j
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      congr 1
      ring
    · push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      ring
  have hz := hasSum_zeta_two.summable.comp_injective
    (show Function.Injective (fun j : ℕ => j + N + 1) by intro a b h; dsimp at h; omega)
  apply hasSum_le _ hz.hasSum hc
  intro j
  have hj : (0 : ℝ) < (j + N : ℕ) := by positivity
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  nlinarith

private lemma quotient_square_defect (N d : ℕ) (hN : 0 < N) (hd : 0 < d) :
    0 ≤ 1 / (d : ℝ)^2 - ((N / d : ℕ) : ℝ)^2 / (N : ℝ)^2 ∧
      1 / (d : ℝ)^2 - ((N / d : ℕ) : ℝ)^2 / (N : ℝ)^2 ≤ 2 / ((N : ℝ) * d) := by
  have hNr : (0 : ℝ) < N := by positivity
  have hdr : (0 : ℝ) < d := by positivity
  have hlo : (d : ℝ) * (N / d : ℕ) ≤ N := by exact_mod_cast Nat.mul_div_le N d
  have hhi : (N : ℝ) < (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ N hd
  have ht : (0 : ℝ) ≤ d * (N / d : ℕ) := by positivity
  have hsq := mul_self_le_mul_self ht hlo
  have hprod := mul_nonneg
    (show (0 : ℝ) ≤ d - ((N : ℝ) - d * (N / d : ℕ)) by linarith)
    (show (0 : ℝ) ≤ N + d * (N / d : ℕ) by positivity)
  have hat := mul_le_mul_of_nonneg_left hlo hdr.le
  have hnum : (N : ℝ)^2 - ((d : ℝ) * (N / d : ℕ))^2 ≤ 2 * N * d := by nlinarith
  have he : 1 / (d : ℝ)^2 - ((N / d : ℕ) : ℝ)^2 / (N : ℝ)^2 =
      ((N : ℝ)^2 - ((d : ℝ) * (N / d : ℕ))^2) / ((d : ℝ)^2 * (N : ℝ)^2) := by
    field_simp
    <;> ring
  rw [he]
  constructor
  · exact div_nonneg (by nlinarith) (by positivity)
  · calc
      _ ≤ (2 * (N : ℝ) * d) / ((d : ℝ)^2 * (N : ℝ)^2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = _ := by field_simp

private lemma mu_floor_square_bound (N : ℕ) (hN : 0 < N) :
    ‖(∑ d ∈ Icc 1 N, mu d * (((N / d : ℕ) : ℝ) / N)^2) - muSeriesZero‖ ≤
      (2 * (harmonic N : ℝ) + 1) / N := by
  have hNr : (0 : ℝ) < N := by positivity
  have hs0 : Summable (fun n : ℕ => mu n / (n : ℝ)^2) :=
    (summable_nat_add_iff 1).mp mu_square_summable
  have hpartial : (∑ d ∈ range (N + 1), mu d / (d : ℝ)^2) =
      ∑ d ∈ Icc 1 N, mu d / (d : ℝ)^2 := by
    symm
    apply sum_subset
    · intro d hd
      have := mem_Icc.mp hd
      exact mem_range.mpr (by omega)
    · intro d hd hnot
      have hz : d = 0 := by simp only [mem_range, mem_Icc] at *; omega
      simp [hz]
  have hsplit := hs0.sum_add_tsum_nat_add (N + 1)
  rw [hpartial] at hsplit
  simp only [← Nat.add_assoc] at hsplit
  change (∑ d ∈ Icc 1 N, mu d / (d : ℝ)^2) +
    (∑' j : ℕ, mu (j + N + 1) / ((j + N + 1 : ℕ) : ℝ)^2) = muSeriesZero at hsplit
  have hts : Summable (fun j : ℕ => mu (j + N + 1) / ((j + N + 1 : ℕ) : ℝ)^2) :=
    hs0.comp_injective (by intro a b h; dsimp at h; omega)
  have hps := hasSum_zeta_two.summable.comp_injective
    (show Function.Injective (fun j : ℕ => j + N + 1) by intro a b h; dsimp at h; omega)
  have htail : ‖∑' j : ℕ, mu (j + N + 1) / ((j + N + 1 : ℕ) : ℝ)^2‖ ≤ 1 / (N : ℝ) := by
    calc
      _ ≤ ∑' j : ℕ, ‖mu (j + N + 1) / ((j + N + 1 : ℕ) : ℝ)^2‖ :=
        norm_tsum_le_tsum_norm hts.norm
      _ ≤ ∑' j : ℕ, 1 / ((j + N + 1 : ℕ) : ℝ)^2 := by
        apply hts.norm.tsum_le_tsum _ hps
        intro j
        rw [norm_div, Real.norm_of_nonneg (sq_nonneg _)]
        exact div_le_div_of_nonneg_right (mu_bound _) (sq_nonneg _)
      _ ≤ _ := reciprocal_square_tail N hN
  have hsingle (d : ℕ) (hd : d ∈ Icc 1 N) :
      ‖mu d * ((((N / d : ℕ) : ℝ) / N)^2 - 1 / (d : ℝ)^2)‖ ≤ 2 / ((N : ℝ) * d) := by
    have hdp : 0 < d := by have := (mem_Icc.mp hd).1; omega
    have hb := quotient_square_defect N d hN hdp
    rw [← div_pow] at hb
    simp only [norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonpos (show (((N / d : ℕ) : ℝ) / N)^2 - 1 / (d : ℝ)^2 ≤ 0 by linarith)]
    calc
      _ ≤ 1 * (1 / (d : ℝ)^2 - (((N / d : ℕ) : ℝ) / N)^2) := by
        have hm : |mu d| ≤ 1 := by simpa only [Real.norm_eq_abs] using mu_bound d
        convert mul_le_mul_of_nonneg_right hm hb.1 using 1 <;> ring
      _ ≤ _ := by simpa using hb.2
  have hsum : ‖∑ d ∈ Icc 1 N, mu d *
      ((((N / d : ℕ) : ℝ) / N)^2 - 1 / (d : ℝ)^2)‖ ≤ 2 / (N : ℝ) * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Icc 1 N, ‖mu d *
          ((((N / d : ℕ) : ℝ) / N)^2 - 1 / (d : ℝ)^2)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Icc 1 N, 2 / ((N : ℝ) * d) := sum_le_sum hsingle
      _ = _ := by
        rw [← harmonic_Icc, mul_sum]
        apply sum_congr rfl
        intro d hd
        ring
  have he : (∑ d ∈ Icc 1 N, mu d * (((N / d : ℕ) : ℝ) / N)^2) - muSeriesZero =
      (∑ d ∈ Icc 1 N, mu d * ((((N / d : ℕ) : ℝ) / N)^2 - 1 / (d : ℝ)^2)) -
        ∑' j : ℕ, mu (j + N + 1) / ((j + N + 1 : ℕ) : ℝ)^2 := by
    simp_rw [mul_sub, sum_sub_distrib, mul_one_div]
    linarith [hsplit]
  rw [he]
  calc
    _ ≤ ‖∑ d ∈ Icc 1 N, mu d * ((((N / d : ℕ) : ℝ) / N)^2 - 1 / (d : ℝ)^2)‖ +
        ‖∑' j : ℕ, mu (j + N + 1) / ((j + N + 1 : ℕ) : ℝ)^2‖ := norm_sub_le _ _
    _ ≤ 2 / (N : ℝ) * (harmonic N : ℝ) + 1 / (N : ℝ) := add_le_add hsum htail
    _ = _ := by ring

private lemma roundingMobius_limit :
    Tendsto (fun N : ℕ => Real.log N *
      ((∑ d ∈ Icc 1 N, mu d * (((N / d : ℕ) : ℝ) / N)^2) - muSeriesZero))
      atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ => (Real.log N)^2 / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one, Function.comp_def] using
      ((isLittleO_log_rpow_rpow_atTop 2 (s := 1) (by norm_num)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop)
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := (hs.const_mul 2).add (hl.const_mul 3)
  apply squeeze_zero_norm' _ (show Tendsto _ atTop (𝓝 0) by simpa using ht)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hNr : (0 : ℝ) < N := by positivity
  rw [norm_mul, Real.norm_of_nonneg hlog]
  calc
    _ ≤ Real.log N * ((2 * (harmonic N : ℝ) + 1) / N) :=
      mul_le_mul_of_nonneg_left (mu_floor_square_bound N (by omega)) hlog
    _ ≤ Real.log N * ((2 * (1 + Real.log N) + 1) / N) := by
      gcongr
      exact harmonic_le_one_add_log N
    _ = _ := by ring

private noncomputable def mobiusPrefix (N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, mu d * weightedPairs (N / d)

private lemma mobiusPrefix_decomposition (N : ℕ) (hN : 0 < N) :
    mobiusPrefix N / (N : ℝ)^2 - (1 / 2 : ℝ) * muSeriesZero * Real.log N =
      (∑' d : ℕ, residualMobiusTerm N d) +
      (1 / 2 : ℝ) * (∑' d : ℕ, logarithmicMobiusTerm N d) +
      (1 / 2 : ℝ) * (Real.log N *
        ((∑ d ∈ Icc 1 N, mu d * (((N / d : ℕ) : ℝ) / N)^2) - muSeriesZero)) := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hr : (∑' d : ℕ, residualMobiusTerm N d) =
      ∑ d ∈ Icc 1 N, residualMobiusTerm N d := by
    apply tsum_eq_sum
    intro d hd
    have hd' : d = 0 ∨ N < d := by simp only [mem_Icc] at hd; omega
    rcases hd' with rfl | hd'
    · simp [residualMobiusTerm, mu]
    · simp [residualMobiusTerm, Nat.div_eq_of_lt hd']
  have hl : (∑' d : ℕ, logarithmicMobiusTerm N d) =
      ∑ d ∈ Icc 1 N, logarithmicMobiusTerm N d := by
    apply tsum_eq_sum
    intro d hd
    have hd' : d = 0 ∨ N < d := by simp only [mem_Icc] at hd; omega
    rcases hd' with rfl | hd'
    · simp [logarithmicMobiusTerm, mu]
    · simp [logarithmicMobiusTerm, Nat.div_eq_of_lt hd']
  have ht (d : ℕ) (hd : d ∈ Icc 1 N) :
      mu d * weightedPairs (N / d) / (N : ℝ)^2 =
        residualMobiusTerm N d + (1 / 2 : ℝ) * logarithmicMobiusTerm N d +
        (1 / 2 : ℝ) * Real.log N * (mu d * (((N / d : ℕ) : ℝ) / N)^2) := by
    have hq : 0 < N / d := Nat.div_pos (mem_Icc.mp hd).2 (mem_Icc.mp hd).1
    have hqr : ((N / d : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp [residualMobiusTerm, logarithmicMobiusTerm, weightedResidual]
    rw [Real.log_div hqr hNr]
    field_simp
    <;> ring
  rw [hr, hl, mobiusPrefix, sum_div]
  rw [sum_congr rfl ht]
  simp only [sum_add_distrib, ← mul_sum]
  ring

private lemma mobiusPrefix_second_term :
    Tendsto (fun N : ℕ => mobiusPrefix N / (N : ℝ)^2 -
      (3 / Real.pi^2) * Real.log N) atTop
      (𝓝 ((3 / Real.pi^2) * (-1 / 2 + 2 * Real.eulerMascheroniConstant -
        6 * deriv realZeta 2 / Real.pi^2))) := by
  have ht := (residualMobius_limit.add (logarithmicMobius_limit.const_mul (1 / 2 : ℝ))).add
    (roundingMobius_limit.const_mul (1 / 2 : ℝ))
  have hv := mu_series_values
  have he : (Real.eulerMascheroniConstant - 1 / 4) * muSeriesZero +
      (1 / 2 : ℝ) * -muSeriesLog + (1 / 2 : ℝ) * 0 =
      (3 / Real.pi^2) * (-1 / 2 + 2 * Real.eulerMascheroniConstant -
        6 * deriv realZeta 2 / Real.pi^2) := by
    rw [hv.1, hv.2]
    ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← mobiusPrefix_decomposition N (by omega), hv.1]
  ring

private lemma pillai_prefix_mobius (N : ℕ) :
    (∑ n ∈ Icc 1 N,
      (D5.S3.Factorization.AlternatingGcdSumPillai.pillai n : ℝ)) = mobiusPrefix N := by
  let i : ArithmeticFunction ℝ := (ArithmeticFunction.id : ArithmeticFunction ℝ)
  let t : ArithmeticFunction ℝ := ⟨fun n => (Nat.totient n : ℝ), by simp⟩
  let m : ArithmeticFunction ℝ := (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
  let z : ArithmeticFunction ℝ := (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have htz : t * z = i := by
    ext n
    change (t * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n = i n
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    change (∑ d ∈ n.divisors, (Nat.totient d : ℝ)) = (n : ℝ)
    exact_mod_cast Nat.sum_totient n
  have hzm : z * m = 1 := ArithmeticFunction.coe_zeta_mul_coe_moebius
  have htm : t = i * m := by
    calc
      t = t * (z * m) := by rw [hzm, mul_one]
      _ = (t * z) * m := (mul_assoc _ _ _).symm
      _ = i * m := by rw [htz]
  have hp (n : ℕ) (hn : 0 < n) :
      (D5.S3.Factorization.AlternatingGcdSumPillai.pillai n : ℝ) =
        (m * (i * i)) n := by
    have hid : t * i = m * (i * i) := by rw [htm]; ac_rfl
    rw [← hid, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => t a * i b)]
    change _ = ∑ d ∈ n.divisors, (Nat.totient d : ℝ) * (n / d : ℕ)
    exact_mod_cast D5.S3.Factorization.AlternatingGcdSumPillai.pillai_divisors n (by omega)
  have hI (X : ℕ) : Ioc 0 X = Icc 1 X := by ext k; simp only [mem_Ioc, mem_Icc]; omega
  have hw (X : ℕ) : (∑ n ∈ Icc 1 X, (i * i) n) = weightedPairs X := by
    rw [← hI, ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter]
    simp only [hI, weightedPairs, i, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.id_apply]
  calc
    _ = ∑ n ∈ Icc 1 N, (m * (i * i)) n := by
      apply sum_congr rfl
      intro n hn
      exact hp n (by have := (mem_Icc.mp hn).1; omega)
    _ = ∑ d ∈ Icc 1 N, m d * ∑ n ∈ Icc 1 (N / d), (i * i) n := by
      simpa only [hI] using ArithmeticFunction.sum_Ioc_mul_eq_sum_sum m (i * i) N
    _ = mobiusPrefix N := by
      simp only [hw, mobiusPrefix, m, mu, ArithmeticFunction.intCoe_apply]

theorem pillai_second_term :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, (D5.S3.Factorization.AlternatingGcdSumPillai.pillai n : ℝ)) /
      (N : ℝ)^2 - (3 / Real.pi^2) * Real.log N) atTop
      (𝓝 ((3 / Real.pi^2) * (-1 / 2 + 2 * Real.eulerMascheroniConstant -
        6 * deriv realZeta 2 / Real.pi^2))) := by
  simpa only [pillai_prefix_mobius] using mobiusPrefix_second_term

end D5.S3.ArithSums.A400361PillaiMean
