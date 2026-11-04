/- GID: D5/S3/Analytic/KummerModulusLowerBound/Result
   generality: I
   mirror-B: D5/B/S3/Analytic/KummerModulusLowerBound/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/KummerModulusLowerBound/Result.claim; result=D5/S3/Analytic/KummerModulusLowerBound/Result.result; claim=D5/S3/Analytic/KummerModulusLowerBound/Result.claim
   digest: An exponential times a quadratic refutes the universal Kummer modulus lower bound. -/

/-
admission_basis: open-problem-resolution (#21791; Refuted).
All theorem rows are bind-only; escape_witness: none for every declaration.
Coefficient multiplication evaluates Mathlib ascPochhammer_mul at −3/2
with lengths (n, 2) and (2, n), then normalizes the resulting identity.
The remaining steps instantiate exponential summation, index shifting,
complex embedding, square-root evaluation and ordered-field normalization.
No row is claimed to supply an escape witness.
Declaration identities from the scoped Lean report:
  C: GID D5/S3/Analytic/KummerRatio/Defs.kummerCoeff
     Lean name D5.S3.Analytic.KummerRatio.Defs.kummerCoeff
     statement_id sha256:2ada6e56e131a4bdb7cccbc60aec3a351bc0b05a8b9544c75077cb676503abe7
  R: GID D5/S3/Analytic/KummerRatio/Defs.kummer
     Lean name D5.S3.Analytic.KummerRatio.Defs.kummer
     statement_id sha256:70196670dff0a16e33b533d05c6452c653b3bb0e8b19dd669e85095852b5f8de
  W: GID D5/S3/Quantum/ResolvedCountWeakValue.weighted_exp_hasSum
     Lean name D5.S3.Quantum.ResolvedCountWeakValue.weighted_exp_hasSum
     statement_id sha256:b29a61138bd3b5679dcf1e943a62a8b1646ad186cd852a2bfaa28923d60c3516
C and R are frozen baseline declarations. W is the public form of the
baseline private declaration in D5/S3/Quantum/ResolvedCountWeakValue:
  _private.D5.S3.Quantum.ResolvedCountWeakValue.0.D5.S3.Quantum.ResolvedCountWeakValue.weighted_exp_hasSum
  baseline declaration statement_id:
    sha256:41eadbf06f11130f333cc4e9eb283cdb9fcb8288f8ce91d8cff74cf1b8b2894e
  shared type_sha256:
    sha256:280a228f8ab62456d9610d4041062e12a4e6870afa0de9eb984968b5c2ee0564
Per declaration: name | proof_shape | consumers | frozen deps / W exposure.
  kummerC | bind-only (definition) | claim, complex_closed, witness_zero, result | C
  claim | bind-only (definition) | result | R, C
  half_ne_nat | bind-only | coeff_eq, result | none
  coeff_eq | bind-only | complex_closed | C
  second_exp_hasSum | bind-only | complex_closed | W
  complex_closed | bind-only | real_closed, witness_zero | C, W
  real_closed | bind-only | witness_pos | R, C, W
  witness_zero | bind-only | result | C, W
  witness_pos | bind-only | result | R, C, W
  result | bind-only | settling result | R, C, W
The only public theorem is the designated result; all helpers have consumers.
The computational utility is certified-instance with basis refutes.
-/

import D5.S3.Analytic.KummerRatio.Defs
import D5.S3.Quantum.ResolvedCountWeakValue

/-! The quadratic-exponential witness for the Kummer modulus question. -/

noncomputable section
open scoped BigOperators
open D5.S3.Analytic.KummerRatio.Defs
namespace D5.S3.Analytic.KummerModulusLowerBound.Result

def kummerC (a b : ℝ) (z : ℂ) : ℂ := ∑' n, (kummerCoeff a b n : ℂ) * z ^ n

def claim : Prop :=
  ∀ α β : ℝ, 0 < α → 0 < β → (∀ n : ℕ, α - β ≠ -(n : ℝ)) →
    ∀ z : ℂ, kummer α (α - β) z.re ≤ ‖kummerC α (α - β) z‖

private lemma half_ne_nat (n : ℕ) : (-3/2 : ℝ) ≠ -(n : ℝ) := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    linarith

private lemma coeff_eq (n : ℕ) :
    kummerCoeff (1/2) (-3/2) n =
      (1 - (4/3:ℝ)*n + (4/3:ℝ)*n*(n-1)) / (n.factorial : ℝ) := by
  have hp : (ascPochhammer ℝ n).eval (1/2) =
      (1 - (4/3:ℝ)*n + (4/3:ℝ)*n*(n-1)) * (ascPochhammer ℝ n).eval (-3/2) := by
    have h₁ := congrArg (fun p : Polynomial ℝ => p.eval (-3/2)) (ascPochhammer_mul ℝ n 2)
    have h₂ := congrArg (fun p : Polynomial ℝ => p.eval (-3/2)) (ascPochhammer_mul ℝ 2 n)
    simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_natCast] at h₁ h₂
    have htwo (x : ℝ) : (ascPochhammer ℝ 2).eval x = x * (x + 1) := by
      norm_num [ascPochhammer_succ_eval]
    rw [htwo] at h₁ h₂
    norm_num at h₁ h₂ ⊢
    rw [Nat.add_comm 2 n] at h₂
    linear_combination (4/3:ℝ) * (h₂ - h₁)
  have hd : (ascPochhammer ℝ n).eval (-3/2) ≠ 0 := by
    rw [ne_eq, ascPochhammer_eval_eq_zero_iff n (-3/2:ℝ)]
    rintro ⟨k, _, hk⟩
    exact half_ne_nat k (by linarith)
  unfold kummerCoeff
  rw [hp]
  rw [mul_comm ((ascPochhammer ℝ n).eval (-3/2)) _, mul_div_mul_right _ _ hd]

private lemma second_exp_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => (n:ℂ) * (n-1:ℂ) * z^n / (n.factorial:ℂ))
      (z^2 * Complex.exp z) := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, zero_div, sub_zero]
  convert (D5.S3.Quantum.ResolvedCountWeakValue.weighted_exp_hasSum z).mul_left z using 1
  · ext n
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hn : (n:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero n
    field_simp
    ring
  · ring

private lemma complex_closed (z : ℂ) :
    kummerC (1/2) (-3/2) z = Complex.exp z * (1 - 4*z/3 + 4*z^2/3) := by
  have h0 : HasSum (fun n : ℕ => z^n / (n.factorial:ℂ)) (Complex.exp z) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp z
  have h1 := D5.S3.Quantum.ResolvedCountWeakValue.weighted_exp_hasSum z
  have h2 := second_exp_hasSum z
  have hs := (h0.sub (h1.mul_left (4/3:ℂ))).add (h2.mul_left (4/3:ℂ))
  convert hs.tsum_eq using 1
  · apply tsum_congr
    intro n
    rw [coeff_eq]
    push_cast
    ring
  · ring

private lemma real_closed (x : ℝ) :
    kummer (1/2) (-3/2) x = Real.exp x * (1 - 4*x/3 + 4*x^2/3) := by
  apply Complex.ofReal_injective
  push_cast
  rw [kummer, Complex.ofReal_tsum]
  simpa only [kummerC, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp] using complex_closed (x:ℂ)

private lemma witness_zero :
    kummerC (1/2) (-3/2) ((1/2:ℂ) + (Real.sqrt 2 / 2 : ℝ) * Complex.I) = 0 := by
  rw [complex_closed]
  suffices 1 - 4*((1/2:ℂ)+(Real.sqrt 2/2:ℝ)*Complex.I)/3 +
      4*((1/2:ℂ)+(Real.sqrt 2/2:ℝ)*Complex.I)^2/3 = 0 by rw [this, mul_zero]
  apply Complex.ext <;> simp [pow_two] <;> nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

private lemma witness_pos : 0 < kummer (1/2) (-3/2) (1/2) := by
  rw [real_closed]
  norm_num
  positivity

theorem result : ¬ claim := by
  intro h
  have hc : kummer (1/2) (-3/2) (1/2) ≤
      ‖kummerC (1/2) (-3/2) ((1/2:ℂ) + (Real.sqrt 2/2:ℝ)*Complex.I)‖ := by
    convert h (1/2) 2 (by norm_num) (by norm_num)
      (fun n => by convert half_ne_nat n using 1; ring)
      ((1/2:ℂ) + (Real.sqrt 2/2:ℝ)*Complex.I) using 1 <;> norm_num
  rw [witness_zero, norm_zero] at hc
  exact (not_le_of_gt witness_pos) hc

end D5.S3.Analytic.KummerModulusLowerBound.Result
