/- GID: D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/BinetPositiveResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Binet logarithmic kernel supplies signed budgets and a positive response. -/

import D5.S3.Arith.SignedDirichletPositiveResponse
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.BinetPositiveResponse

open scoped BigOperators

/-- The literal logarithmic Binet coefficient; its zero value is `log 0 = 0`. -/
noncomputable def beta (q : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log (1 - (-q) ^ n), by simp⟩

/-- The complete negative tail, indexed by positive even indices. -/
noncomputable def negativeTail (q : ℝ) : ℝ :=
  ∑' j : ℕ, -beta q (2 * (j + 1))

/-- The complete positive tail after the head, indexed by odd indices at least three. -/
noncomputable def positiveTail (q : ℝ) : ℝ :=
  ∑' j : ℕ, beta q (2 * (j + 1) + 1)

/-- The existing Dirichlet inverse applied to the existing arithmetic logarithm. -/
noncomputable def response (q : ℝ) (hq : 0 < q) : ArithmeticFunction ℝ :=
  ArithmeticFunction.dirichletInverse (beta q)
    (invertibleOfNonzero (by
      have h := Real.log_pos (show 1 < 1 + q by linarith)
      simpa [beta] using ne_of_gt h)) * ArithmeticFunction.log

private theorem beta_even (q : ℝ) (j : ℕ) :
    beta q (2 * (j + 1)) = Real.log (1 - q ^ (2 * (j + 1))) := by
  simp [beta, (even_two_mul (j + 1)).neg_pow]

private theorem beta_odd (q : ℝ) (j : ℕ) :
    beta q (2 * (j + 1) + 1) = Real.log (1 + q ^ (2 * (j + 1) + 1)) := by
  have ho : Odd (2 * (j + 1) + 1) := ⟨j + 1, rfl⟩
  simp [beta, ho.neg_pow]

private theorem signed_tail_contract (q : ℝ) (hq : 0 < q) (hqmax : q ≤ 2 / 5) :
    Summable (fun j : ℕ => -beta q (2 * (j + 1))) ∧
    Summable (fun j : ℕ => beta q (2 * (j + 1) + 1)) ∧
    (∀ n : ℕ, (∑ d ∈ n.divisors.erase 1, max (-beta q d) 0) ≤ negativeTail q) ∧
    (∀ n : ℕ, (∑ d ∈ n.divisors.erase 1, max (beta q d) 0) ≤ positiveTail q) ∧
    94 * q / 2205 ≤ beta q 1 - negativeTail q - positiveTail q := by
  have hq1 : q < 1 := by linarith
  have hq2 : q ^ 2 < 1 := pow_lt_one₀ hq.le hq1 (by decide)
  have hden : 0 < 1 - q ^ 2 := by linarith
  let A : ℕ → ℝ := fun j => -beta q (2 * (j + 1))
  let C : ℕ → ℝ := fun j => beta q (2 * (j + 1) + 1)
  have hAnonneg : ∀ j, 0 ≤ A j := by
    intro j
    have hpow : q ^ (2 * (j + 1)) < 1 := pow_lt_one₀ hq.le hq1 (by omega)
    have hlog := Real.log_nonpos (by linarith : 0 ≤ 1 - q ^ (2 * (j + 1)))
      (by nlinarith [pow_nonneg hq.le (2 * (j + 1))] : 1 - q ^ (2 * (j + 1)) ≤ 1)
    simpa [A, beta_even] using neg_nonneg.mpr hlog
  have hCnonneg : ∀ j, 0 ≤ C j := by
    intro j
    simpa [C, beta_odd] using Real.log_nonneg
      (by nlinarith [pow_nonneg hq.le (2 * (j + 1) + 1)] :
        1 ≤ 1 + q ^ (2 * (j + 1) + 1))
  have hAbound : ∀ j, A j ≤ (q ^ 2 / (1 - q ^ 2)) * (q ^ 2) ^ j := by
    intro j
    have hpow : q ^ (2 * (j + 1)) < 1 := pow_lt_one₀ hq.le hq1 (by omega)
    have hle : q ^ (2 * (j + 1)) ≤ q ^ 2 :=
      pow_le_pow_of_le_one hq.le hq1.le (by omega)
    have hlog := Real.one_sub_inv_le_log_of_pos
      (by linarith : 0 < 1 - q ^ (2 * (j + 1)))
    have halgebra : (1 - q ^ (2 * (j + 1)))⁻¹ - 1 =
        q ^ (2 * (j + 1)) / (1 - q ^ (2 * (j + 1))) := by
      field_simp [ne_of_gt (show 0 < 1 - q ^ (2 * (j + 1)) by linarith)]
      ring
    calc
      A j ≤ q ^ (2 * (j + 1)) / (1 - q ^ (2 * (j + 1))) := by
        dsimp [A]
        rw [beta_even]
        rw [← halgebra]
        linarith
      _ ≤ q ^ (2 * (j + 1)) / (1 - q ^ 2) :=
        div_le_div_of_nonneg_left (pow_nonneg hq.le _) hden (by linarith)
      _ = (q ^ 2 / (1 - q ^ 2)) * (q ^ 2) ^ j := by
        rw [pow_mul, pow_succ]
        ring
  have hCbound : ∀ j, C j ≤ q ^ 3 * (q ^ 2) ^ j := by
    intro j
    have hlog := Real.log_le_sub_one_of_pos
      (by nlinarith [pow_nonneg hq.le (2 * (j + 1) + 1)] :
        0 < 1 + q ^ (2 * (j + 1) + 1))
    calc
      C j ≤ q ^ (2 * (j + 1) + 1) := by
        dsimp [C]
        rw [beta_odd]
        linarith
      _ = q ^ 3 * (q ^ 2) ^ j := by
        rw [pow_succ, pow_mul, pow_succ]
        ring
  have hgeo := summable_geometric_of_lt_one (sq_nonneg q) hq2
  have hAsum : Summable A :=
    Summable.of_nonneg_of_le hAnonneg hAbound (hgeo.mul_left _)
  have hCsum : Summable C :=
    Summable.of_nonneg_of_le hCnonneg hCbound (hgeo.mul_left _)
  have hEbound : negativeTail q ≤ q ^ 2 / (1 - q ^ 2) ^ 2 := by
    have h := hAsum.tsum_le_tsum hAbound (hgeo.mul_left _)
    rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg q) hq2] at h
    simpa [negativeTail, A, div_eq_mul_inv, pow_two, mul_assoc] using h
  have hPbound : positiveTail q ≤ q ^ 3 / (1 - q ^ 2) := by
    have h := hCsum.tsum_le_tsum hCbound (hgeo.mul_left _)
    simpa [positiveTail, C, tsum_mul_left,
      tsum_geometric_of_lt_one (sq_nonneg q) hq2, div_eq_mul_inv] using h
  let u : ℕ → ℝ := fun m => max (-beta q (m + 2)) 0
  let v : ℕ → ℝ := fun m => max (beta q (m + 2)) 0
  have hueven : (fun j => u (2 * j)) = A := by
    funext j
    have he : 2 * j + 2 = 2 * (j + 1) := by omega
    simp only [u, he]
    exact max_eq_left (hAnonneg j)
  have huodd : (fun j => u (2 * j + 1)) = fun _ => 0 := by
    funext j
    have he : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by omega
    simp only [u, he]
    exact max_eq_right (neg_nonpos.mpr (hCnonneg j))
  have hveven : (fun j => v (2 * j)) = fun _ => 0 := by
    funext j
    have he : 2 * j + 2 = 2 * (j + 1) := by omega
    simp only [v, he]
    exact max_eq_right (by simpa [A] using neg_nonneg.mp (hAnonneg j))
  have hvodd : (fun j => v (2 * j + 1)) = C := by
    funext j
    have he : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by omega
    simp only [v, he]
    exact max_eq_left (hCnonneg j)
  have husum : Summable u := by
    apply Summable.even_add_odd
    · rwa [hueven]
    · rw [huodd]; exact summable_zero
  have hvsum : Summable v := by
    apply Summable.even_add_odd
    · rw [hveven]; exact summable_zero
    · rwa [hvodd]
  have hutail : (∑' m, u m) = negativeTail q := by
    have h := tsum_even_add_odd
      (show Summable (fun j => u (2 * j)) by rwa [hueven])
      (show Summable (fun j => u (2 * j + 1)) by rw [huodd]; exact summable_zero)
    simpa [hueven, huodd, negativeTail, A] using h.symm
  have hvtail : (∑' m, v m) = positiveTail q := by
    have h := tsum_even_add_odd
      (show Summable (fun j => v (2 * j)) by rw [hveven]; exact summable_zero)
      (show Summable (fun j => v (2 * j + 1)) by rwa [hvodd])
    simpa [hveven, hvodd, positiveTail, C] using h.symm
  have hfinite (w : ℕ → ℝ) (hw : Summable w) (hw0 : ∀ m, 0 ≤ w m) (n : ℕ) :
      (∑ d ∈ n.divisors.erase 1, w (d - 2)) ≤ ∑' m, w m := by
    have hinj : ∀ d ∈ n.divisors.erase 1, ∀ e ∈ n.divisors.erase 1,
        d - 2 = e - 2 → d = e := by
      intro d hd e he hde
      have hdpos := Nat.pos_of_mem_divisors (Finset.mem_erase.mp hd).2
      have hepos := Nat.pos_of_mem_divisors (Finset.mem_erase.mp he).2
      have hd1 := (Finset.mem_erase.mp hd).1
      have he1 := (Finset.mem_erase.mp he).1
      omega
    rw [← Finset.sum_image hinj]
    exact hw.sum_le_tsum _ (fun m _ => hw0 m)
  have hnfinite : ∀ n : ℕ,
      (∑ d ∈ n.divisors.erase 1, max (-beta q d) 0) ≤ negativeTail q := by
    intro n
    have h := hfinite u husum (fun m => le_max_right _ _) n
    rw [hutail] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos := Nat.pos_of_mem_divisors (Finset.mem_erase.mp hd).2
    have hd1 := (Finset.mem_erase.mp hd).1
    have he : d - 2 + 2 = d := Nat.sub_add_cancel (by omega)
    simp [u, he]
  have hpfinite : ∀ n : ℕ,
      (∑ d ∈ n.divisors.erase 1, max (beta q d) 0) ≤ positiveTail q := by
    intro n
    have h := hfinite v hvsum (fun m => le_max_right _ _) n
    rw [hvtail] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos := Nat.pos_of_mem_divisors (Finset.mem_erase.mp hd).2
    have hd1 := (Finset.mem_erase.mp hd).1
    have he : d - 2 + 2 = d := Nat.sub_add_cancel (by omega)
    simp [v, he]
  have hqsmall : q ^ 2 ≤ 4 / 25 := by nlinarith
  have hdenlarge : 21 / 25 ≤ 1 - q ^ 2 := by linarith
  have hhead : (4 / 5 : ℝ) * q ≤ beta q 1 := by
    have h := Real.le_log_one_add_of_nonneg hq.le
    have hr : (4 / 5 : ℝ) * q ≤ 2 * q / (q + 2) := by
      apply (le_div_iff₀ (by linarith : 0 < q + 2)).mpr
      nlinarith
    simpa [beta] using hr.trans h
  have hEB : q ^ 2 / (1 - q ^ 2) ^ 2 ≤ (250 / 441 : ℝ) * q := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    have hs : (441 / 625 : ℝ) ≤ (1 - q ^ 2) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hs)]
  have hPB : q ^ 3 / (1 - q ^ 2) ≤ (4 / 21 : ℝ) * q := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hqsmall)]
  exact ⟨hAsum, hCsum, hnfinite, hpfinite, by linarith⟩

/-- The actual infinite signed tails supply every premise of the positive
response theorem, with the exact tail constants in the resulting bounds. -/
theorem binet_response_contract (q : ℝ) (hq : 0 < q) (hqmax : q ≤ 2 / 5) :
    Summable (fun j : ℕ => -beta q (2 * (j + 1))) ∧
    Summable (fun j : ℕ => beta q (2 * (j + 1) + 1)) ∧
    94 * q / 2205 ≤ beta q 1 - negativeTail q - positiveTail q ∧
    (∀ n : ℕ,
      (∑ d ∈ n.divisors.erase 1, max (-beta q d) 0) ≤ negativeTail q ∧
      (∑ d ∈ n.divisors.erase 1, max (beta q d) 0) ≤ positiveTail q) ∧
    response q hq 1 = 0 ∧
    (∀ n : ℕ, 0 < n →
      ((beta q 1 - negativeTail q - positiveTail q) /
        (beta q 1 * (beta q 1 - negativeTail q))) * Real.log n ≤ response q hq n ∧
      response q hq n ≤ Real.log n / (beta q 1 - negativeTail q)) ∧
    (∀ n : ℕ, 1 < n → 0 < response q hq n) := by
  obtain ⟨hAsum, hCsum, hnfinite, hpfinite, hgapbound⟩ :=
    signed_tail_contract q hq hqmax
  have hgap : negativeTail q + positiveTail q < beta q 1 := by
    have hqgap : 0 < 94 * q / 2205 := by positivity
    linarith
  have hconvolution : beta q * response q hq = ArithmeticFunction.log := by
    rw [response, ← mul_assoc, ArithmeticFunction.self_mul_dirichletInverse, one_mul]
  have hrec : ∀ n : ℕ, 0 < n →
      (∑ d ∈ n.divisors, beta q d * response q hq (n / d)) = Real.log n := by
    intro n hn
    have h := congrArg (fun a : ArithmeticFunction ℝ => a n) hconvolution
    simpa [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun i j => beta q i * response q hq j)] using h
  have hbounds := D5.S3.Arith.SignedDirichletPositiveResponse.signedDivisor_positive_response
    (beta q) (response q hq) (fun n => Real.log n) (negativeTail q) (positiveTail q)
    (fun n hn => Real.log_nonneg (by exact_mod_cast hn))
    (fun m n hm hmn => Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmn))
    hnfinite hpfinite hgap hrec
  have hzero : response q hq 1 = 0 := by
    have h := hbounds 1 (by decide)
    simp only [Nat.cast_one, Real.log_one, mul_zero, zero_div] at h
    exact le_antisymm h.2 h.1
  have hE : 0 ≤ negativeTail q := by simpa using hnfinite 1
  have hP : 0 ≤ positiveTail q := by simpa using hpfinite 1
  have hhead : 0 < beta q 1 := by linarith
  have hden : 0 < beta q 1 - negativeTail q := by linarith
  have hmargin : 0 < beta q 1 - negativeTail q - positiveTail q := by linarith
  have hstrict : ∀ n : ℕ, 1 < n → 0 < response q hq n := by
    intro n hn
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hlower := (hbounds n (by omega)).1
    exact (mul_pos (div_pos hmargin (mul_pos hhead hden)) hlog).trans_le hlower
  exact ⟨hAsum, hCsum, hgapbound, fun n => ⟨hnfinite n, hpfinite n⟩,
    hzero, hbounds, hstrict⟩

end D5.S3.Arith.FibonacciAtomic.BinetPositiveResponse
