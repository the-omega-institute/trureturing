/- Transient anonymous applications of the whole original formula.
   UNCOMPILED. All finite Mangoldt weights and all zero occurrences remain.
   No application declaration is proposed for canonical installation. -/
import D5.S3.Weil.Mertens.IntegratedExplicit.WholeFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Arith.Robin.CompleteMertensPeak
open scoped BigOperators

/-- Original actual application: the complete all-occurrence HasSum equals
the existing complete finite U and the entire trivial-zero correction. -/
example {y : ℝ} (hy : 0 < y) :
    HasSum (fun k : ℕ => (1 / (actualZero k * (1 - actualZero k))) *
      Complex.exp ((y : ℂ) * actualZero k))
      ((U (Real.exp y) - Real.log (2 * Real.pi) +
        ∑' n : ℕ, Real.exp (-(2 * ((n : ℝ) + 1)) * y) /
          (2 * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 1)) : ℝ) : ℂ) := by
  have hT : trivialT y =
      ∑' n : ℕ, Real.exp (-(2 * ((n : ℝ) + 1)) * y) /
        (2 * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 1)) := by
    apply tsum_congr
    intro n
    dsimp only [trivialCoeff]
    ring
  rw [← hT, ← actual_integrated_explicit_formula hy]
  exact (actualH_summable y).hasSum

/-- Real identity for the same complete actual series, with genuine convergence. -/
example {y : ℝ} (hy : 0 < y) :
    (actualH y).im = 0 ∧
      (actualH y).re = U (Real.exp y) - Real.log (2 * Real.pi) + trivialT y := by
  refine ⟨actualH_im y, ?_⟩
  simpa only [Complex.ofReal_re] using
    congrArg Complex.re (actual_integrated_explicit_formula hy)

/-- Exact finite integer endpoint application. This includes every prime-power
endpoint and the endpoint 5040 by the same theorem, with all Mangoldt terms. -/
example (N : ℕ) (hN : 2 ≤ N) :
    HasSum (fun k : ℕ => (1 / (actualZero k * (1 - actualZero k))) *
      Complex.exp ((Real.log N : ℂ) * actualZero k))
      (((∑ n ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt n * ((N : ℝ) / (n : ℝ) - 1)) -
          (N : ℝ) * Real.log N + (1 + Real.eulerMascheroniConstant) * N -
            Real.log (2 * Real.pi) + trivialT (Real.log N) : ℝ) : ℂ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have he := actual_integrated_explicit_formula hlog
  rw [Real.exp_log hN0, (complete_mangoldt_endpoint N (by omega)).2.2] at he
  rw [← he]
  exact (actualH_summable (Real.log N)).hasSum


/-- Explicit anonymous full finite check at the requested integer 5040. -/
example :
    HasSum (fun k : ℕ => (1 / (actualZero k * (1 - actualZero k))) *
      Complex.exp ((Real.log (5040 : ℝ) : ℂ) * actualZero k))
      (((∑ n ∈ Finset.Ioc 0 5040,
        ArithmeticFunction.vonMangoldt n * ((5040 : ℝ) / (n : ℝ) - 1)) -
          (5040 : ℝ) * Real.log (5040 : ℝ) + (1 + Real.eulerMascheroniConstant) * (5040 : ℝ) -
            Real.log (2 * Real.pi) + trivialT (Real.log (5040 : ℝ)) : ℝ) : ℂ) := by
  have hlog : 0 < Real.log (5040 : ℝ) := Real.log_pos (by norm_num)
  have he := actual_integrated_explicit_formula hlog
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 5040),
    (complete_mangoldt_endpoint 5040 (by norm_num)).2.2] at he
  rw [← he]
  exact (actualH_summable (Real.log (5040 : ℝ))).hasSum

/-- Every prime-power endpoint p^(k+1), with its entering term retained. -/
example (p : ℕ) (hp : Nat.Prime p) (m : ℕ) :
    HasSum (fun k : ℕ => (1 / (actualZero k * (1 - actualZero k))) *
      Complex.exp ((Real.log ((p ^ (m + 1) : ℕ) : ℝ) : ℂ) * actualZero k))
      (((∑ n ∈ Finset.Ioc 0 (p ^ (m + 1)),
        ArithmeticFunction.vonMangoldt n * (((p ^ (m + 1) : ℕ) : ℝ) / (n : ℝ) - 1)) -
          ((p ^ (m + 1) : ℕ) : ℝ) * Real.log ((p ^ (m + 1) : ℕ) : ℝ) +
            (1 + Real.eulerMascheroniConstant) * ((p ^ (m + 1) : ℕ) : ℝ) -
              Real.log (2 * Real.pi) + trivialT (Real.log ((p ^ (m + 1) : ℕ) : ℝ)) : ℝ) : ℂ) := by
  let N : ℕ := p ^ (m + 1)
  have hpow : 0 < p ^ m := pow_pos hp.pos m
  have hN : 2 ≤ N := by
    dsimp only [N]
    rw [pow_succ]
    exact hp.two_le.trans (by
      simpa only [one_mul] using
        Nat.mul_le_mul_right p (show 1 ≤ p ^ m by omega))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have he := actual_integrated_explicit_formula hlog
  rw [Real.exp_log hN0, (complete_mangoldt_endpoint N (by omega)).2.2] at he
  rw [← he]
  exact (actualH_summable (Real.log N)).hasSum

/-- Literal numerator/denominator form of the whole original target. -/
example {y : ℝ} (hy : 0 < y) :
    HasSum (fun k : ℕ => Complex.exp ((y : ℂ) * actualZero k) /
      (actualZero k * (1 - actualZero k)))
      ((U (Real.exp y) - Real.log (2 * Real.pi) +
        ∑' n : ℕ, Real.exp (-(2 * ((n : ℝ) + 1)) * y) /
          (2 * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 1)) : ℝ) : ℂ) := by
  have h := (actualH_summable y).hasSum
  change HasSum (fun k : ℕ => actualCoeff k * Complex.exp ((y : ℂ) * actualZero k))
    (actualH y) at h
  rw [actual_integrated_explicit_formula hy] at h
  dsimp only [actualCoeff, trivialT, trivialCoeff] at h
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

end
