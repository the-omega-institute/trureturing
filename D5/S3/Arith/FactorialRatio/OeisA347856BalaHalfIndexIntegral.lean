/- GID: D5/S3/Arith/FactorialRatio/OeisA347856BalaHalfIndexIntegral
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/OeisA347856BalaHalfIndexIntegral
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala's A347856 fractional-factorial integrality. -/

/-
escape_witness: none
admission_basis: open-problem-resolution (#18694; Proved)
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

namespace D5.S3.Arith.FactorialRatio.OeisA347856BalaHalfIndexIntegral

open D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

/-- A347856: `a(n) = (6*n)!/((4*n)!*n!) * (n/2)!/(3*n/2)!`. -/
noncomputable def a (n : ℕ) : ℝ :=
  (Nat.factorial (6 * n) : ℝ) / ((Nat.factorial (4 * n) : ℝ) * (Nat.factorial n : ℝ)) *
    (ffact ((n : ℝ) / 2) / ffact (3 * (n : ℝ) / 2))

/-- A347856 ("The sequence is conjectured to be integral."). -/
def claim : Prop := ∀ n : ℕ, ∃ z : ℤ, (z : ℝ) = a n

end D5.S3.Arith.FactorialRatio.OeisA347856BalaHalfIndexIntegral

set_option maxHeartbeats 800000

namespace D5.S3.Arith.FactorialRatio.OeisA347856BalaHalfIndexIntegral
open D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

private lemma even_dvd (m : ℕ) : (8*m).factorial*(2*m).factorial*(3*m).factorial ∣ (12*m).factorial*(1*m).factorial := by
    have hh := factorial_prod_dvd_of_floor [12*m, 1*m] [8*m, 2*m, 3*m]
      (by
        intro q hq
        have hc := h856_nonneg m q hq
        simp only [h856] at hc
        simpa [add_assoc] using (show 8*m/q + 2*m/q + 3*m/q ≤ 12*m/q + 1*m/q by omega))
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc] using hh

private lemma even_formula (m : ℕ) : a (2*m) = (((12*m).factorial : ℝ)*((1*m).factorial : ℝ)) / (((8*m).factorial : ℝ)*((2*m).factorial : ℝ)*((3*m).factorial : ℝ)) := by
    simp only [a, ffact, Nat.cast_mul, Nat.cast_ofNat]
    rw [show (2*(m : ℝ))/2 = m by ring, show (3 : ℝ)*(2*m)/2 = (3*m) by ring]
    rw [gamma_nat, show (3 : ℝ)*(m : ℝ) = ((3*m : ℕ) : ℝ) by push_cast; ring, gamma_nat]
    norm_num [show 6*(2*m) = 12*m by omega, show 4*(2*m) = 8*m by omega, show 1*(2*m) = 2*m by omega]
    field_simp

private lemma odd_dvd (n : ℕ) : (4*n).factorial*(3*n).factorial*(n/2).factorial ∣ (6*n).factorial*(3*n/2).factorial := by
    have hh := factorial_prod_dvd_of_floor [6*n, 3*n/2] [4*n, 3*n, n/2]
      (by
        intro q hq
        have hc := k856_nonneg n (2*q) (by omega)
        simp only [k856] at hc
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.div_div_eq_div_mul]
        have g3 : 3*n/q = 6*n/(2*q) := by
          simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using
            grid_floor 6 3 2 n q hq (by decide) (by decide)
        have g4 : 4*n/q = 8*n/(2*q) := by
          simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using
            grid_floor 8 4 2 n q hq (by decide) (by decide)
        have g6 : 6*n/q = 12*n/(2*q) := by
          simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using
            grid_floor 12 6 2 n q hq (by decide) (by decide)
        simp only [Nat.one_mul] at *
        omega)
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc] using hh

private lemma odd_formula (n : ℕ) (hn : n % 2 = 1) : a n = (2 : ℝ)^(2*n) * ((((6*n).factorial : ℝ)*((3*n/2).factorial : ℝ)) / (((4*n).factorial : ℝ)*((3*n).factorial : ℝ)*((n/2).factorial : ℝ))) := by
    have hr : (1*n) % 2 = 1 := Nat.odd_mul_odd rfl hn
    have hs : (3*n) % 2 = 1 := Nat.odd_mul_odd rfl hn
    have hratio := gamma_ratio_half (1*n) (3*n) hr hs (by omega)
    rw [show 3*n-1*n = 2*n by omega] at hratio
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

end D5.S3.Arith.FactorialRatio.OeisA347856BalaHalfIndexIntegral
