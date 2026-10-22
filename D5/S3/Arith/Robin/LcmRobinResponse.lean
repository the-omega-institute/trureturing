/- GID: D5/S3/Arith/Robin/LcmRobinResponse
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mertens.E₃ gives the common Robin response of the actual prefix lcm. -/

import D5.S3.Arith.Robin.PrimeFiberPropagation
import D5.S3.Weil.Mertens.Third
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! The actual prefix lcm has an exact prime-factor Euler product.  The omitted
prime-power layers are bounded by a square-root tail, which combines with the
Mertens third-theorem error and the tangent bound for `log log`. -/

namespace D5.S3.Arith.Robin.LcmRobinResponse

open scoped BigOperators
open Finset Real
open Chebyshev
open D5.S3.Arith.Robin.PrimeFiberPropagation

noncomputable section

private abbrev primeCutoff (u : ℝ) : Finset ℕ := (Ioc 0 ⌊u⌋₊).filter Nat.Prime

private abbrev tailFactor (u : ℝ) (p : ℕ) : ℝ :=
  1 / (p : ℝ) ^ (p.log ⌊u⌋₊ + 1)

private theorem sigma_lcm_euler_product {u : ℝ} (hu : 2 ≤ u) :
    (ArithmeticFunction.sigma 1 (Nat.lcmUpto ⌊u⌋₊) : ℝ) /
        (Nat.lcmUpto ⌊u⌋₊ : ℝ) =
      ∏ p ∈ primeCutoff u,
        (1 - tailFactor u p) / (1 - 1 / (p : ℝ)) := by
  let n := ⌊u⌋₊
  have hn : n ≠ 0 := by
    have : 2 ≤ n := by
      exact Nat.le_floor hu
    omega
  have hprod : (ArithmeticFunction.sigma 1 (Nat.lcmUpto n) : ℝ) =
      ∏ p ∈ (Nat.lcmUpto n).primeFactors,
        ∑ i ∈ range ((Nat.lcmUpto n).factorization p + 1), (p : ℝ) ^ i := by
    simpa only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, mul_one] using
      congrArg (fun k : ℕ => (k : ℝ))
        (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
          (k := 1) (Nat.lcmUpto_ne_zero n))
  have hnprod : (Nat.lcmUpto n : ℝ) =
      ∏ p ∈ (Nat.lcmUpto n).primeFactors,
        (p : ℝ) ^ (Nat.lcmUpto n).factorization p := by
    simpa only [Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun k : ℕ => (k : ℝ))
        (Nat.prod_primeFactors_pow_factorization (Nat.lcmUpto_ne_zero n))
  have hfactor (p : ℕ) (hp : p.Prime) (a : ℕ) :
      ((∑ i ∈ range (a + 1), (p : ℝ) ^ i) / (p : ℝ) ^ a) =
        (1 - (1 : ℝ) / (p : ℝ) ^ (a + 1)) / (1 - 1 / (p : ℝ)) := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [geom_sum_eq hp1.ne']
    field_simp
    ring
  rw [hprod, hnprod, ← prod_div_distrib]
  rw [Nat.primeFactors_lcmUpto]
  have hset : Nat.primesLE n = primeCutoff u := by
    ext p
    simp only [primeCutoff, mem_filter, Nat.mem_primesLE, mem_Ioc]
    constructor
    · rintro ⟨hp, hpn⟩
      exact ⟨⟨hpn.pos, hp⟩, hpn⟩
    · rintro ⟨⟨hp0, hpn⟩, hp⟩
      exact ⟨hpn, hp⟩
  rw [hset]
  apply prod_congr rfl
  intro p hp
  rw [Nat.factorization_lcmUpto n (mem_filter.mp hp).2]
  exact hfactor p (mem_filter.mp hp |>.2) _

private theorem loglog_tangent {u v : ℝ} (hu : 1 < u) (hv : 1 < v) :
    Real.log (Real.log v) ≤ Real.log (Real.log u) + (v - u) / (u * Real.log u) := by
  have hLu : 0 < Real.log u := Real.log_pos hu
  have hLv : 0 < Real.log v := Real.log_pos hv
  have hratio : 0 < Real.log v / Real.log u := div_pos hLv hLu
  have hlog1 := Real.log_le_sub_one_of_pos hratio
  have huv : 0 < v / u := div_pos (by linarith) (by linarith)
  have hlog2 := Real.log_le_sub_one_of_pos huv
  have hEq1 : Real.log (Real.log v) - Real.log (Real.log u) =
      Real.log (Real.log v / Real.log u) := by
    rw [Real.log_div hLv.ne' hLu.ne']
  have hEq2 : Real.log (v / u) = Real.log v - Real.log u := by
    rw [Real.log_div (by linarith) (by linarith)]
  have hlog2' : Real.log (v / u) / Real.log u ≤
      (v / u - 1) / Real.log u :=
    div_le_div_of_nonneg_right hlog2 hLu.le
  have hratio' : Real.log v / Real.log u - 1 =
      (Real.log v - Real.log u) / Real.log u := by field_simp
  calc
    Real.log (Real.log v) = Real.log (Real.log u) +
        Real.log (Real.log v / Real.log u) := by linarith [hEq1]
    _ ≤ Real.log (Real.log u) +
        (Real.log v / Real.log u - 1) := by linarith
    _ = Real.log (Real.log u) + Real.log (v / u) / Real.log u := by
      rw [hratio', hEq2]
    _ ≤ Real.log (Real.log u) + (v / u - 1) / Real.log u :=
      by simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hlog2' (Real.log (Real.log u))
    _ = Real.log (Real.log u) + (v - u) / (u * Real.log u) := by
      field_simp

private theorem log_tail_le {z : ℝ} (hz0 : 0 < z) (hz4 : z ≤ 1 / 4) :
    -Real.log (1 - z) ≤ (4 / 3) * z := by
  have hz1 : z < 1 := by linarith
  have hpos : 0 < 1 / (1 - z) := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (sub_ne_zero.mpr hz1.ne')] at h
  simp only [Real.log_one, zero_sub] at h
  have h' : -Real.log (1 - z) ≤ z / (1 - z) := by
    convert h using 1 <;> field_simp <;> ring
  have hfrac : z / (1 - z) ≤ (4 / 3) * z := by
    have hden : 0 < 1 - z := by linarith
    apply (div_le_iff₀ hden).2
    nlinarith
  exact h'.trans hfrac

private theorem lcm_tail_bound {u : ℝ} (hu : 10000 ≤ u) :
    -∑ p ∈ primeCutoff u, Real.log (1 - tailFactor u p) ≤ 4 / Real.sqrt u := by
  let n := ⌊u⌋₊
  let S := primeCutoff u
  let N := ⌊Real.sqrt u⌋₊ + 1
  have hn : 10000 ≤ n := by exact Nat.le_floor hu
  have hu0 : 0 < u := by linarith
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hsmall (p : ℕ) (hp : p ∈ S) (hps : (p : ℝ) ≤ Real.sqrt u) :
      tailFactor u p < 1 / u := by
    change p ∈ (Ioc 0 n).filter Nat.Prime at hp
    have hpp : p.Prime := mem_filter.mp hp |>.2
    have hp_le_n : p ≤ n := (mem_Ioc.mp (mem_filter.mp hp).1).2
    have hp_le_nR : (p : ℝ) ≤ n := by exact_mod_cast hp_le_n
    have hp_le_u : (p : ℝ) ≤ u := hp_le_nR.trans (Nat.floor_le (by linarith))
    have hp1 : 1 < p := hpp.one_lt
    have hp0 : p ≠ 0 := Nat.ne_of_gt hpp.pos
    have ha : 0 < p.log n := Nat.log_pos hp1 (by
      exact Nat.le_floor hp_le_u)
    have hpow : n < p ^ (p.log n + 1) := by
      simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hp1 n
    have hnpow : n + 1 ≤ p ^ (p.log n + 1) := by omega
    have huN : u < (n + 1 : ℕ) := by
      simpa [n] using Nat.lt_floor_add_one u
    have hpowR : u < (p : ℝ) ^ (p.log n + 1) := by
      exact lt_of_lt_of_le huN (by exact_mod_cast hnpow)
    have hpPow : 0 < (p : ℝ) ^ (p.log n + 1) := by positivity
    exact (div_lt_div_iff₀ hpPow (by linarith)).2 (by linarith)
  have hlarge (p : ℕ) (hp : p ∈ S) (hps : Real.sqrt u < p) :
      tailFactor u p ≤ 1 / (p : ℝ) ^ 2 := by
    change p ∈ (Ioc 0 n).filter Nat.Prime at hp
    have hpp := mem_filter.mp hp |>.2
    have hp_le_n : p ≤ n := (mem_Ioc.mp (mem_filter.mp hp).1).2
    have hp_le_nR : (p : ℝ) ≤ n := by exact_mod_cast hp_le_n
    have hp_le_u : (p : ℝ) ≤ u := hp_le_nR.trans (Nat.floor_le (by linarith))
    have hapos : 0 < p.log n := Nat.log_pos hpp.one_lt (Nat.le_floor hp_le_u)
    have ha : 1 ≤ p.log n := by omega
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hpow : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (p.log n + 1) := by
      apply pow_le_pow_right₀ hp1
      omega
    have hp2 : 0 < (p : ℝ) ^ 2 := by positivity
    have hpPow : 0 < (p : ℝ) ^ (p.log n + 1) := by positivity
    exact (div_le_div_iff₀ hpPow hp2).2 (by simpa using hpow)
  have htailquarter (p : ℕ) (hp : p ∈ S) : tailFactor u p ≤ 1 / 4 := by
    change p ∈ (Ioc 0 n).filter Nat.Prime at hp
    have hpp := mem_filter.mp hp |>.2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp_le_n : p ≤ n := (mem_Ioc.mp (mem_filter.mp hp).1).2
    have hp_le_nR : (p : ℝ) ≤ n := by exact_mod_cast hp_le_n
    have hp_le_u : (p : ℝ) ≤ u := hp_le_nR.trans (Nat.floor_le (by linarith))
    have hapos : 0 < p.log n := Nat.log_pos hpp.one_lt (Nat.le_floor hp_le_u)
    have ha : 1 ≤ p.log n := by omega
    have hpow : (4 : ℝ) ≤ (p : ℝ) ^ (p.log n + 1) := by
      calc
        (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
        _ ≤ (p : ℝ) ^ (p.log n + 1) := by
          apply pow_le_pow_right₀ (by linarith)
          omega
    have hpPow : 0 < (p : ℝ) ^ (p.log n + 1) := by positivity
    exact (div_le_iff₀ hpPow).2 (by linarith)
  have hlogpoint (p : ℕ) (hp : p ∈ S) :
      -Real.log (1 - tailFactor u p) ≤ (4 / 3) * tailFactor u p :=
    by
      change p ∈ (Ioc 0 n).filter Nat.Prime at hp
      have hpp : p.Prime := (mem_filter.mp hp).2
      have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      apply log_tail_le
      · change 0 < 1 / (p : ℝ) ^ (p.log n + 1)
        positivity
      · exact htailquarter p hp
  have hsmallset : S.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt u) ⊆
      Ioc 0 ⌊Real.sqrt u⌋₊ := by
    intro p hp
    have h := mem_filter.mp hp
    have hpS : p ∈ (Ioc 0 n).filter Nat.Prime := by
      simpa [S, primeCutoff] using h.1
    have hs := mem_filter.mp hpS
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hs.1).1, Nat.le_floor h.2⟩
  have hsmall_sum : ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt u),
      tailFactor u p ≤ 1 / Real.sqrt u := by
    have hcard : ((S.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt u)).card : ℝ) ≤ Real.sqrt u := by
      calc
        _ ≤ ((Ioc 0 ⌊Real.sqrt u⌋₊).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsmallset
        _ = (⌊Real.sqrt u⌋₊ : ℝ) := by simp
        _ ≤ Real.sqrt u := Nat.floor_le hsqrt.le
    have hsum := sum_le_card_nsmul _ (fun p => tailFactor u p) (1 / u) (by
      intro p hp
      exact (hsmall p (mem_filter.mp hp).1 (mem_filter.mp hp).2).le)
    have htailnonneg : 0 ≤ (1 / u : ℝ) := by positivity
    rw [nsmul_eq_mul] at hsum
    calc
      _ ≤ ((S.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt u)).card : ℝ) * (1 / u) := hsum
      _ ≤ Real.sqrt u * (1 / u) := mul_le_mul_of_nonneg_right hcard htailnonneg
      _ = 1 / Real.sqrt u := by
        field_simp [ne_of_gt hsqrt, ne_of_gt hu0]
        rw [Real.sq_sqrt hu0.le]
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hNsqrt : Real.sqrt u ≤ (N : ℝ) := by
    dsimp [N]
    simpa [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (Real.sqrt u)).le
  have hNn : N ≤ n + 1 := by
    have hsu : Real.sqrt u ≤ u := by
      nlinarith [Real.sq_sqrt hu0.le, Real.sqrt_nonneg u]
    have : ⌊Real.sqrt u⌋₊ + 1 ≤ n + 1 := by
      apply Nat.add_le_add_right
      exact Nat.floor_mono (by simpa [n] using hsu)
    exact this
  have hlargeset : S.filter (fun p : ℕ => Real.sqrt u < (p : ℝ)) ⊆ Ico N (n + 1) := by
    intro p hp
    have h := mem_filter.mp hp
    have hpNat : N ≤ p := by
      dsimp [N]
      have hfloor : ⌊Real.sqrt u⌋₊ < p := (Nat.floor_lt hsqrt.le).2 (mem_filter.mp hp).2
      omega
    have hpUpper : p < n + 1 := by
      have := mem_Ioc.mp (mem_filter.mp h.1).1 |>.2
      exact Nat.lt_succ_of_le this
    exact mem_Ico.mpr ⟨hpNat, hpUpper⟩
  have hlarge_sum : ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt u < (p : ℝ)),
      tailFactor u p ≤ 2 / Real.sqrt u := by
    have hsubset_sum :
        ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt u < (p : ℝ)), 1 / (p : ℝ) ^ 2 ≤
          ∑ p ∈ Ico N (n + 1), 1 / (p : ℝ) ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg hlargeset
      intro p hp hnot
      positivity
    have hshift : (∑ p ∈ Ico N (n + 1), 1 / (p : ℝ) ^ 2) =
        ∑ k ∈ range (n + 1 - N), 1 / ((k + N : ℕ) : ℝ) ^ 2 := by
      have h := sum_Ico_add' (fun p : ℕ => 1 / (p : ℝ) ^ 2) 0 (n + 1 - N) N
      simpa [Nat.zero_add, Nat.sub_add_cancel hNn] using h.symm
    have hsumm : Summable (fun k : ℕ => 1 / ((k + N : ℕ) : ℝ) ^ 2) := by
      simpa [Nat.cast_add] using
        (summable_nat_add_iff N).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
    have hpartial := hsumm.sum_le_tsum (range (n + 1 - N)) (by intro k hk; positivity)
    have hM := Mertens.sum_one_div_sq_le (N := (N : ℝ)) (by exact_mod_cast hN)
    have hM' : (∑' k : ℕ, 1 / ((k + N : ℕ) : ℝ) ^ 2) ≤ 2 / (N : ℝ) := by
      simpa [Nat.cast_add] using hM
    have htaillarge :
        ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt u < (p : ℝ)), tailFactor u p ≤
          ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt u < (p : ℝ)), 1 / (p : ℝ)^2 :=
      sum_le_sum fun p hp => hlarge p (mem_filter.mp hp).1 (mem_filter.mp hp).2
    calc
      _ ≤ ∑ p ∈ S.filter (fun p : ℕ => Real.sqrt u < (p : ℝ)), 1 / (p : ℝ)^2 := htaillarge
      _ ≤ ∑ p ∈ Ico N (n + 1), 1 / (p : ℝ) ^ 2 := hsubset_sum
      _ = ∑ k ∈ range (n + 1 - N), 1 / ((k + N : ℕ) : ℝ) ^ 2 := hshift
      _ ≤ ∑' k : ℕ, 1 / ((k + N : ℕ) : ℝ) ^ 2 := hpartial
      _ ≤ 2 / (N : ℝ) := hM'
      _ ≤ 2 / Real.sqrt u := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith [hNsqrt]
  have htailsum : ∑ p ∈ S, tailFactor u p ≤ 3 / Real.sqrt u := by
    rw [← sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ Real.sqrt u)]
    have hnot : S.filter (fun p : ℕ => ¬(p : ℝ) ≤ Real.sqrt u) =
        S.filter (fun p : ℕ => Real.sqrt u < (p : ℝ)) := by
      ext p; simp only [mem_filter, not_le]
    rw [hnot]
    calc
      _ ≤ (1 / Real.sqrt u) + (2 / Real.sqrt u) :=
        add_le_add hsmall_sum hlarge_sum
      _ = 3 / Real.sqrt u := by ring
  calc
    -∑ p ∈ S, Real.log (1 - tailFactor u p) =
        ∑ p ∈ S, -Real.log (1 - tailFactor u p) := by
      simp only [Finset.sum_neg_distrib]
    _ ≤ ∑ p ∈ S, (4 / 3) * tailFactor u p := sum_le_sum fun p hp => hlogpoint p hp
    _ = (4 / 3) * ∑ p ∈ S, tailFactor u p := by
      rw [Finset.mul_sum]
    _ ≤ (4 / 3) * (3 / Real.sqrt u) := mul_le_mul_of_nonneg_left htailsum (by norm_num)
    _ = 4 / Real.sqrt u := by ring

private theorem lcm_log_identities {u : ℝ} (hu : 10000 ≤ u) :
    let D := Nat.lcmUpto ⌊u⌋₊
    5040 < D ∧ Real.log (D : ℝ) = ψ u ∧ (D : ℝ) ≤ Real.exp (u * Real.log u) := by
  dsimp
  let n := ⌊u⌋₊
  have hn : 10000 ≤ n := Nat.le_floor hu
  have hndvd : n ∣ Nat.lcmUpto n := by
    unfold Nat.lcmUpto
    have hn0 : n ≠ 0 := by omega
    exact Finset.dvd_lcm (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, le_rfl⟩)
  have hDge : n ≤ Nat.lcmUpto n := Nat.le_of_dvd (Nat.lcmUpto_pos n) hndvd
  have hlog : Real.log (Nat.lcmUpto n : ℝ) = ψ u := by
    rw [← Chebyshev.psi_eq_log_lcmUpto, ← Chebyshev.psi_eq_psi_coe_floor]
  have hψle : ψ u ≤ u * Real.log u := by
    have hmain := Chebyshev.psi_le (x := u) (by linarith)
    have hu0 : 0 < u := by linarith
    have hlog16le : Real.log 16 ≤ Real.log u := by
      exact Real.strictMonoOn_log.monotoneOn (show (0 : ℝ) < 16 by norm_num)
        (show (0 : ℝ) < u by linarith) (show (16 : ℝ) ≤ u by linarith)
    have hlog16 : Real.log 16 = 2 * Real.log 4 := by
      rw [show (16 : ℝ) = 4 * 4 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    have hlog4half : Real.log 4 ≤ Real.log u / 2 := by
      nlinarith [hlog16le, hlog16]
    have hsqrt4 : 4 * Real.sqrt u ≤ u := by
      nlinarith [Real.sq_sqrt hu0.le, Real.sqrt_nonneg u]
    have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    have h1 : Real.log 4 * u ≤ (u * Real.log u) / 2 := by
      have h := mul_le_mul_of_nonneg_right hlog4half hu0.le
      nlinarith
    have h2 : 2 * Real.sqrt u * Real.log u ≤ (u * Real.log u) / 2 := by
      have hhalf : 2 * Real.sqrt u ≤ u / 2 := by nlinarith [hsqrt4]
      have h := mul_le_mul_of_nonneg_right hhalf hlogu
      nlinarith
    calc
      ψ u ≤ Real.log 4 * u + 2 * Real.sqrt u * Real.log u := hmain
      _ ≤ (u * Real.log u) / 2 + (u * Real.log u) / 2 := add_le_add h1 h2
      _ = u * Real.log u := by ring
  have hDpos : 0 < (Nat.lcmUpto n : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos n
  have hDexp : (Nat.lcmUpto n : ℝ) ≤ Real.exp (u * Real.log u) := by
    rw [← Real.exp_log hDpos, hlog]
    exact Real.exp_le_exp.mpr hψle
  have hstrict : (5040 : ℕ) < Nat.lcmUpto n := by omega
  exact ⟨hstrict, hlog, hDexp⟩

theorem common_robin_response {u : ℝ} (hu : 10000 ≤ u) :
    let D := Nat.lcmUpto ⌊u⌋₊
    divisorRatio D ≤ Real.exp Real.eulerMascheroniConstant * Real.log (Real.log D) →
      Mertens.E₃ u ≥ -4 / Real.sqrt u -
        (Chebyshev.psi u - u) / (u * Real.log u) := by
  dsimp
  let n := ⌊u⌋₊
  let D := Nat.lcmUpto n
  intro hRobin
  have hids := lcm_log_identities hu
  have hlogD : Real.log (D : ℝ) = ψ u := hids.2.1
  have hDpos : 0 < (D : ℝ) := by
    dsimp [D]
    exact_mod_cast Nat.lcmUpto_pos n
  have hu1 : 1 < u := by linarith
  have hψ1 : 1 < ψ u := by
    rw [← hlogD]
    apply (Real.lt_log_iff_exp_lt hDpos).2
    have hDstrict : (5040 : ℕ) < D := by simpa [D, n] using hids.1
    have h9 : (9 : ℝ) ≤ D := by
      exact_mod_cast (show (9 : ℕ) ≤ D by omega)
    calc
      Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ < (9 : ℝ) := by norm_num
      _ ≤ (D : ℝ) := h9
  have hlogbound : Real.log (Real.log (ψ u)) ≤
      Real.log (Real.log u) + (ψ u - u) / (u * Real.log u) :=
    loglog_tangent hu1 hψ1
  have htail := lcm_tail_bound hu
  have hprod := sigma_lcm_euler_product (u := u) (by linarith)
  have hlogratio : Real.log (divisorRatio D) =
      -Mertens.E₃ u + Real.log (Real.log u) + Real.eulerMascheroniConstant -
        (-∑ p ∈ primeCutoff u, Real.log (1 - tailFactor u p)) := by
    unfold divisorRatio
    change Real.log ((ArithmeticFunction.sigma 1 (Nat.lcmUpto n) : ℝ) /
      (Nat.lcmUpto n : ℝ)) = _
    have hquarter_of_mem (p : ℕ) (hp : p ∈ primeCutoff u) :
        tailFactor u p ≤ 1 / 4 := by
      change p ∈ (Ioc 0 n).filter Nat.Prime at hp
      have hpp := mem_filter.mp hp |>.2
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have hp_le_n : p ≤ n := (mem_Ioc.mp (mem_filter.mp hp).1).2
      have hp_le_nR : (p : ℝ) ≤ n := by exact_mod_cast hp_le_n
      have hp_le_u : (p : ℝ) ≤ u :=
        hp_le_nR.trans (Nat.floor_le (by linarith))
      have hapos : 0 < p.log n := Nat.log_pos hpp.one_lt (Nat.le_floor hp_le_u)
      have ha : 1 ≤ p.log n := by omega
      have hpow : (4 : ℝ) ≤ (p : ℝ) ^ (p.log n + 1) := by
        calc
          (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
          _ ≤ (p : ℝ) ^ (p.log n + 1) := by
            apply pow_le_pow_right₀ (by linarith)
            omega
      exact (div_le_iff₀ (show 0 < (p : ℝ) ^ (p.log n + 1) by positivity)).2
        (by linarith)
    rw [hprod, Real.log_prod]
    · unfold Mertens.E₃
      calc
        (∑ p ∈ primeCutoff u,
            Real.log ((1 - tailFactor u p) / (1 - 1 / (p : ℝ)))) =
            ∑ p ∈ primeCutoff u,
              (Real.log (1 - tailFactor u p) - Real.log (1 - 1 / (p : ℝ))) := by
          apply Finset.sum_congr rfl
          intro p hp
          change p ∈ (Ioc 0 n).filter Nat.Prime at hp
          have hpp : p.Prime := (mem_filter.mp hp).2
          have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
          have hnum : 0 < 1 - tailFactor u p := by
            linarith [hquarter_of_mem p hp]
          have hden : 0 < 1 - 1 / (p : ℝ) := by
            have hpdiv : 1 / (p : ℝ) < 1 :=
              (div_lt_iff₀ (show 0 < (p : ℝ) by positivity)).2 (by linarith)
            linarith
          rw [Real.log_div hnum.ne' hden.ne']
        _ = (∑ p ∈ primeCutoff u, Real.log (1 - tailFactor u p)) -
            ∑ p ∈ primeCutoff u, Real.log (1 - 1 / (p : ℝ)) := by
          rw [Finset.sum_sub_distrib]
        _ = -(∑ p ∈ primeCutoff u, Real.log (1 - 1 / (p : ℝ)) +
              Real.log (Real.log u) + Real.eulerMascheroniConstant) +
            Real.log (Real.log u) + Real.eulerMascheroniConstant -
            -∑ p ∈ primeCutoff u, Real.log (1 - tailFactor u p) := by ring
    · intro p hp
      change p ∈ (Ioc 0 n).filter Nat.Prime at hp
      have hpp := mem_filter.mp hp |>.2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have hp_le_n : p ≤ n := (mem_Ioc.mp (mem_filter.mp hp).1).2
      have hp_le_nR : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp_le_n
      have hn_le_u : (n : ℝ) ≤ u := Nat.floor_le (by linarith)
      have hp_le_u : (p : ℝ) ≤ u := hp_le_nR.trans hn_le_u
      have hapos : 0 < p.log n := Nat.log_pos hpp.one_lt (Nat.le_floor hp_le_u)
      have ha : 1 ≤ p.log n := by omega
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have hquarter : tailFactor u p ≤ 1 / 4 := hquarter_of_mem p hp
      have hnum : 0 < 1 - tailFactor u p := by linarith
      have hden : 0 < 1 - 1 / (p : ℝ) := by
        have hpdiv : 1 / (p : ℝ) < 1 :=
          (div_lt_iff₀ (show 0 < (p : ℝ) by positivity)).2 (by linarith)
        linarith
      exact div_ne_zero hnum.ne' hden.ne'
  have hlogRobin : Real.log (divisorRatio D) ≤
      Real.eulerMascheroniConstant + Real.log (Real.log (ψ u)) := by
    have hratioPos : 0 < divisorRatio D :=
      divisorRatio_pos (Nat.lcmUpto_ne_zero _)
    have hrightPos : 0 < Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log (D : ℝ)) := by
      apply mul_pos (Real.exp_pos _)
      apply Real.log_pos
      rw [hlogD]
      linarith
    have hRobinD : divisorRatio D ≤ Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log (D : ℝ)) := by
      simpa [D, n] using hRobin
    have hlogRobinD := Real.strictMonoOn_log.monotoneOn hratioPos hrightPos hRobinD
    calc
      Real.log (divisorRatio D) ≤
          Real.log (Real.exp Real.eulerMascheroniConstant *
            Real.log (Real.log (D : ℝ))) := hlogRobinD
      _ = Real.eulerMascheroniConstant + Real.log (Real.log (ψ u)) := by
        rw [Real.log_mul (Real.exp_ne_zero _) (by
          apply ne_of_gt
          rw [hlogD]
          exact Real.log_pos hψ1), Real.log_exp, hlogD]
  rw [hlogratio] at hlogRobin
  let T : ℝ := -∑ p ∈ primeCutoff u, Real.log (1 - tailFactor u p)
  have htailT : T ≤ 4 / Real.sqrt u := by
    simpa [T] using htail
  have hlogRobinT : -Mertens.E₃ u + Real.log (Real.log u) +
      Real.eulerMascheroniConstant - T ≤
      Real.eulerMascheroniConstant + Real.log (Real.log (ψ u)) := by
    simpa [T] using hlogRobin
  have hstep : -Mertens.E₃ u ≤
      (ψ u - u) / (u * Real.log u) + T := by
    linarith [hlogbound, hlogRobinT]
  have hstep' : -Mertens.E₃ u ≤
      (ψ u - u) / (u * Real.log u) + 4 / Real.sqrt u := by
    linarith [hstep, htailT]
  have hneg := neg_le_neg hstep'
  calc
    -4 / Real.sqrt u - (ψ u - u) / (u * Real.log u) =
        -((ψ u - u) / (u * Real.log u) + 4 / Real.sqrt u) := by ring
    _ ≤ - -Mertens.E₃ u := hneg
    _ = Mertens.E₃ u := by ring

theorem common_robin_response_contrapositive {u : ℝ} (hu : 10000 ≤ u)
    (hE : Mertens.E₃ u < -4 / Real.sqrt u -
      (Chebyshev.psi u - u) / (u * Real.log u)) :
    let D := Nat.lcmUpto ⌊u⌋₊
    divisorRatio D > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log D) ∧
      5040 < D ∧ Real.log D = Chebyshev.psi u ∧
      (D : ℝ) ≤ Real.exp (u * Real.log u) := by
  dsimp
  let D := Nat.lcmUpto ⌊u⌋₊
  have hids := lcm_log_identities hu
  have hweak := common_robin_response hu
  have hnot : ¬ divisorRatio D ≤ Real.exp Real.eulerMascheroniConstant * Real.log (Real.log D) := by
    intro h
    have := hweak h
    linarith
  exact ⟨lt_of_not_ge hnot, hids.1, hids.2.1, hids.2.2⟩

end
end D5.S3.Arith.Robin.LcmRobinResponse
