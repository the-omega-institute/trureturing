/- GID: D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala's A347857 fractional-factorial integrality. -/

/-
escape_witness: none
admission_basis: open-problem-resolution (#18695; Proved)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19874
The fractional factorial and sequence definitions retain the source expressions.
No finite computational declaration refutes the claim; utility is none.
Declarations (all dependencies outside this delivery are pinned Mathlib):
  a: proof_shape: bind-only; escape_witness: none;
    consumers: claim, even_formula, odd_formula, result. Direct frozen dependencies: none.
  claim: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  even_dvd: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  even_formula: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  odd_dvd: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  odd_formula: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  result: proof_shape: bind-only; escape_witness: none;
    consumers: settling result. Direct frozen dependencies: none.
-/

import D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

set_option autoImplicit false

namespace D5.S3.Arith.FactorialRatio.OeisA347857BalaHalfIndexIntegral

open D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

/-- A347857: `a(n) = (6*n)!/((3*n)!*(2*n)!) * (3*n/2)!/(5*n/2)!`. -/
noncomputable def a (n : ℕ) : ℝ :=
  (Nat.factorial (6 * n) : ℝ) / ((Nat.factorial (3 * n) : ℝ) * (Nat.factorial (2 * n) : ℝ)) *
    (ffact (3 * (n : ℝ) / 2) / ffact (5 * (n : ℝ) / 2))

/-- A347857 ("The sequence is conjectured to be integral."). -/
def claim : Prop := ∀ n : ℕ, ∃ z : ℤ, (z : ℝ) = a n

end D5.S3.Arith.FactorialRatio.OeisA347857BalaHalfIndexIntegral

set_option maxHeartbeats 800000

namespace D5.S3.Arith.FactorialRatio.OeisA347857BalaHalfIndexIntegral
open D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

private lemma even_dvd (m : ℕ) : (6*m).factorial*(4*m).factorial*(5*m).factorial ∣ (12*m).factorial*(3*m).factorial := by
    have hh := factorial_prod_dvd_of_floor [12*m, 3*m] [6*m, 4*m, 5*m]
      (by
        intro q hq
        have hc := h857_nonneg m q hq
        simp only [h857] at hc
        simpa [add_assoc] using (show 6*m/q + 4*m/q + 5*m/q ≤ 12*m/q + 3*m/q by omega))
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc] using hh

private lemma even_formula (m : ℕ) : a (2*m) = (((12*m).factorial : ℝ)*((3*m).factorial : ℝ)) / (((6*m).factorial : ℝ)*((4*m).factorial : ℝ)*((5*m).factorial : ℝ)) := by
    simp only [a, ffact, Nat.cast_mul, Nat.cast_ofNat]
    rw [show (3 : ℝ)*(2*m)/2 = (3*m) by ring, show (5 : ℝ)*(2*m)/2 = (5*m) by ring]
    rw [show (3 : ℝ)*(m : ℝ) = ((3*m : ℕ) : ℝ) by push_cast; ring, show (5 : ℝ)*(m : ℝ) = ((5*m : ℕ) : ℝ) by push_cast; ring, gamma_nat, gamma_nat]
    norm_num [show 6*(2*m) = 12*m by omega, show 3*(2*m) = 6*m by omega, show 2*(2*m) = 4*m by omega]
    field_simp

private lemma odd_dvd (n : ℕ) : (2*n).factorial*(5*n).factorial*(3*n/2).factorial ∣ (6*n).factorial*(5*n/2).factorial := by
    have hh := factorial_prod_dvd_of_floor [6*n, 5*n/2] [2*n, 5*n, 3*n/2]
      (by
        intro q hq
        have hc := k857_nonneg n (2*q) (by omega)
        simp only [k857] at hc
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.div_div_eq_div_mul]
        have g2 : 2*n/q = 4*n/(2*q) := by
          simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using
            grid_floor 4 2 2 n q hq (by decide) (by decide)
        have g5 : 5*n/q = 10*n/(2*q) := by
          simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using
            grid_floor 10 5 2 n q hq (by decide) (by decide)
        have g6 : 6*n/q = 12*n/(2*q) := by
          simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using
            grid_floor 12 6 2 n q hq (by decide) (by decide)
        omega)
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc] using hh

private lemma odd_formula (n : ℕ) (hn : n % 2 = 1) : a n = (2 : ℝ)^(2*n) * ((((6*n).factorial : ℝ)*((5*n/2).factorial : ℝ)) / (((2*n).factorial : ℝ)*((5*n).factorial : ℝ)*((3*n/2).factorial : ℝ))) := by
    have hr : (3*n) % 2 = 1 := Nat.odd_mul_odd rfl hn
    have hs : (5*n) % 2 = 1 := Nat.odd_mul_odd rfl hn
    have hratio := gamma_ratio_half (3*n) (5*n) hr hs (by omega)
    rw [show 5*n-3*n = 2*n by omega] at hratio
    simp only [Nat.cast_mul, Nat.cast_ofNat, one_mul] at hratio
    simp only [a, ffact]
    rw [hratio]
    field_simp

theorem result : claim := by
    intro n
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have he : n = 2*(n/2) := by omega
      rw [he, even_formula]
      obtain ⟨z, hz⟩ := quotient_cast_integral (even_dvd (n/2)) (by positivity)
      exact ⟨z, by simpa only [Nat.cast_mul] using hz⟩
    · rw [odd_formula n hn]
      obtain ⟨z, hz⟩ := quotient_cast_integral (odd_dvd n) (by positivity)
      refine ⟨(2 : ℤ)^(2*n)*z, ?_⟩
      push_cast
      rw [hz]
      push_cast
      ring

end D5.S3.Arith.FactorialRatio.OeisA347857BalaHalfIndexIntegral
