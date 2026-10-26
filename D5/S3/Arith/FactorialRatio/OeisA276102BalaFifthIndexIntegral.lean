/- GID: D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala A276102 integrality at every natural index. -/
/- escape_witness: none
admission_basis: open-problem-resolution (#21666; Proved)
Direct frozen dependencies: declaration statement_ids are listed per declaration.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21712
  a: Direct frozen dependencies: none; proof_shape: bind-only; escape_witness: none; consumers: claim, a_formula, multiple_formula. claim: Direct frozen dependencies: none; proof_shape: bind-only; escape_witness: none; consumers: result.
  a_formula: Direct frozen dependencies: D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.gamma_shift_product [sha256:6517f62c7c80056802b298d90f84d911ed7d49b29d306b5d64d2ebb8de39f3e9]; proof_shape: bind-only; escape_witness: none; consumers: result. multiple_formula: Direct frozen dependencies: none; proof_shape: bind-only; escape_witness: none; consumers: result.
  result: Direct frozen dependencies: D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.bala_five_integrality [sha256:3e2d5f42dd7144ba1552ae8375b786e0fb26a427c8949ec94a2cbcf3457c52d9]; D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.gamma_shift_product [sha256:6517f62c7c80056802b298d90f84d911ed7d49b29d306b5d64d2ebb8de39f3e9]; D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.grid_floor [sha256:e963adde13e1fbae007e049b0ccb577832f09cabe40e61c63d54ebfb82f2b952]; D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.mul_div_reduce [sha256:efd40ec129eaf47b98931b54d218f23ba6af1038ded8e8765adab500e978e1c9]; D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.quotient_cast_integral [sha256:b533be952af020be1d656bd9f901c785871ba09c5551733ebab4e1c2e0527e46]; D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.padic_eq_card [sha256:e4281962b49fa51ec1364954053a1b0e8f1c72b92d6a15bbba18f4b776f0c204]; D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.padic_finset_prod [sha256:c47bf88627299240e509a07dcd3b58785e73ab4ee9b88013f9786c295bffd815]; proof_shape: bind-only; escape_witness: none; consumers: none (settling result). -/
import D5.S3.Arith.FactorialRatio.OeisA276101BalaThirdIndexIntegral
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace D5.S3.Arith.FactorialRatio.OeisA276102BalaFifthIndexIntegral
open D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral
open D5.S3.Arith.FactorialRatio.OeisA276101BalaThirdIndexIntegral
noncomputable def a (n : ℕ) : ℝ :=
  ((6 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 5 + 1) /
    (((3 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) *
      Real.Gamma ((6 * (n : ℝ)) / 5 + 1))
def claim : Prop := ∀ n : ℕ, ∃ z : ℤ, a n = (z : ℝ)
private lemma a_formula (n : ℕ) : a n = (5 : ℝ)^(1*n) *
    ((6*n).factorial : ℝ) /
      ((3*n).factorial * ((2*n).factorial : ℝ) * progression 5 1 n) := by
  have hr := gamma_ratio 5 1 n (by decide)
  norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at hr
  calc
    a n = ((6*n).factorial : ℝ) / ((3*n).factorial * ((2*n).factorial : ℝ)) *
        (Real.Gamma ((n : ℝ)/5+1) / Real.Gamma ((6*(n : ℝ))/5+1)) := by
      unfold a
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [hr]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
private lemma multiple_formula (m : ℕ) : a (5*m) =
    ((30*m).factorial : ℝ) * m.factorial /
      ((15*m).factorial * ((10*m).factorial : ℝ) * ((6*m).factorial : ℝ)) := by
  unfold a
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [show (5*(m : ℝ))/5+1 = m+1 by ring,
    show (6*(5*(m : ℝ)))/5+1 = (6*m : ℕ)+1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  norm_num [show 6*(5*m) = 30*m by omega,
    show 3*(5*m) = 15*m by omega,
    show 2*(5*m) = 10*m by omega]
theorem result : claim := by
  intro n
  by_cases hn : 5 ∣ n
  · obtain ⟨m,rfl⟩ := hn
    rw [multiple_formula]
    obtain ⟨z,hz⟩ := quotient_cast_integral (ordinary_dvd m) (by positivity)
    exact ⟨z, by simpa only [Nat.cast_mul] using hz.symm⟩
  · rw [a_formula]
    obtain ⟨z,hz⟩ := quotient_cast_integral
      (nonmultiple_dvd 5 6 3 2 1 n (by norm_num [Parameters]) hn)
      (by have := progression_ne_zero 5 1 n (by decide); positivity)
    refine ⟨(5 : ℤ)^(1*n)*z, ?_⟩
    push_cast
    rw [hz]
    push_cast
    ring
end D5.S3.Arith.FactorialRatio.OeisA276102BalaFifthIndexIntegral
