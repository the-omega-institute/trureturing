/- GID: D5/S3/Quantum/Algebra/CStarDualMeanValue
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CStarDualMeanValue
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CStarDualMeanValue.claim; result=D5/S3/Quantum/Algebra/CStarDualMeanValue.result; claim=D5/S3/Quantum/Algebra/CStarDualMeanValue.claim
   digest: A cubic in the product of two complex fields refutes the dual mean value bound. -/

/-
proof_shape: poly_formula: bind-only (consumer: quotient_one, quotient_three)
proof_shape: deriv_formula: bind-only (consumer: critical_set, deriv_at_zero)
proof_shape: critical_set: bind-only (consumer: result)
proof_shape: deriv_at_zero: bind-only (consumer: deriv_at_zero_ne, deriv_norm_at_zero)
proof_shape: deriv_at_zero_ne: bind-only (consumer: result)
proof_shape: deriv_norm_at_zero: bind-only (consumer: quotient_one_lt_threshold, quotient_three_lt_threshold)
proof_shape: quotient_one: bind-only (consumer: quotient_one_lt_threshold)
proof_shape: quotient_three: bind-only (consumer: quotient_three_lt_threshold)
proof_shape: quotient_one_lt_threshold: bind-only (consumer: result)
proof_shape: quotient_three_lt_threshold: bind-only (consumer: result)
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#14940; Refuted)
Direct frozen dependencies:
D5/S3/Quantum/Algebra/CStarSchoenberg.orderedDeriv
  statement_id: sha256:ce1938b197e00c32d6073b1ab7f80e347fafc998daeebfbe011a7ba6ce98cba7
The algebra is restricted to unital commutative C*-algebras in Type. This weakens
the source's universal assertion, so its negation refutes the source statement.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The ordered product and critical-point conventions are those of #14940.
All proof steps instantiate Mathlib facts or normalize the explicit coordinates.
-/

import D5.S3.Quantum.Algebra.CStarSchoenberg

noncomputable section
open scoped BigOperators
open D5.S3.Quantum.Algebra.CStarSchoenberg (orderedDeriv)
namespace D5.S3.Quantum.Algebra.CStarDualMeanValue

def orderedPoly {A : Type} [Ring A] {d : ℕ} (a : Fin d → A) (z : A) : A :=
  (List.ofFn fun i => z - a i).prod

private def aa : Fin 3 → (ℂ × ℂ) := ![((0:ℂ), (3/2:ℂ)), (3, 3/2), (3, 3/2)]

def claim : Prop :=
  ∀ (A : Type) [CommCStarAlgebra A] (n : ℕ), 2 ≤ n → ∀ (a : Fin n → A) (z : A),
    orderedDeriv a z ≠ 0 →
    ∃ w : A, orderedDeriv a w = 0 ∧
      ‖orderedDeriv a z‖ / (n : ℝ) ≤ ‖orderedPoly a z - orderedPoly a w‖ / ‖z - w‖

private theorem poly_formula (x y : ℂ) : orderedPoly aa (x,y) =
    (x * (x - 3)^2, (y - 3/2)^3) := by
  simp [orderedPoly, aa, List.ofFn_succ, pow_two] <;> ring

private theorem deriv_formula (x y : ℂ) : orderedDeriv aa (x,y) =
    (3 * (x - 1) * (x - 3), 3 * (y - 3/2)^2) := by
  simp [orderedDeriv, aa, Fin.sum_univ_succ, List.ofFn_succ, pow_two] <;> ring <;> simp

private theorem critical_set (w : ℂ × ℂ) : orderedDeriv aa w = 0 ↔
    w = ((1:ℂ), (3/2:ℂ)) ∨ w = ((3:ℂ), (3/2:ℂ)) := by
  rcases w with ⟨x,y⟩
  rw [deriv_formula]
  constructor
  · intro h
    have hx0 : 3 * (x - 1) * (x - 3) = 0 := congrArg Prod.fst h
    have hy0 : 3 * (y - 3 / 2) ^ 2 = 0 := congrArg Prod.snd h
    have hxp : (x - 1) * (x - 3) = 0 := by
      rcases mul_eq_zero.mp hx0 with hp | hx3
      · rcases mul_eq_zero.mp hp with h3 | hx1
        · norm_num at h3
        · simp [hx1]
      · simp [hx3]
    have hy2 : (y - 3 / 2) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hy0 with h3 | hp
      · norm_num at h3
      · exact hp
    have hy : y = 3 / 2 := by
      have hy' := (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp hy2
      exact sub_eq_zero.mp hy'
    rcases mul_eq_zero.mp hxp with hx1 | hx3
    · left
      apply Prod.ext
      · exact sub_eq_zero.mp hx1
      · exact hy
    · right
      apply Prod.ext
      · exact sub_eq_zero.mp hx3
      · exact hy
  · intro h
    rcases h with h | h
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp at hx hy
      rw [hx, hy]
      norm_num
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp at hx hy
      rw [hx, hy]
      norm_num

private theorem deriv_at_zero : orderedDeriv aa ((0:ℂ),(0:ℂ)) = ((9:ℂ),(27/4:ℂ)) := by
  rw [deriv_formula]
  norm_num

private theorem deriv_at_zero_ne : orderedDeriv aa ((0:ℂ),(0:ℂ)) ≠ 0 := by
  rw [deriv_at_zero]
  norm_num

private theorem deriv_norm_at_zero : ‖orderedDeriv aa ((0:ℂ),(0:ℂ))‖ = (9 : ℝ) := by
  rw [deriv_at_zero, Prod.norm_def]
  norm_num [Complex.norm_real, Complex.norm_ofNat]

private theorem quotient_one :
    ‖orderedPoly aa ((0:ℂ),(0:ℂ)) - orderedPoly aa ((1:ℂ),(3/2:ℂ))‖ /
      ‖((0:ℂ),(0:ℂ)) - ((1:ℂ),(3/2:ℂ))‖ = (8/3 : ℝ) := by
  rw [poly_formula, poly_formula]
  norm_num [Prod.norm_def, Complex.norm_real, Complex.norm_ofNat]

private theorem quotient_three :
    ‖orderedPoly aa ((0:ℂ),(0:ℂ)) - orderedPoly aa ((3:ℂ),(3/2:ℂ))‖ /
      ‖((0:ℂ),(0:ℂ)) - ((3:ℂ),(3/2:ℂ))‖ = (9/8 : ℝ) := by
  rw [poly_formula, poly_formula]
  norm_num [Prod.norm_def, Complex.norm_real, Complex.norm_ofNat]

private theorem quotient_one_lt_threshold :
    ‖orderedPoly aa ((0:ℂ),(0:ℂ)) - orderedPoly aa ((1:ℂ),(3/2:ℂ))‖ /
      ‖((0:ℂ),(0:ℂ)) - ((1:ℂ),(3/2:ℂ))‖ <
      ‖orderedDeriv aa ((0:ℂ),(0:ℂ))‖ / (3 : ℝ) := by
  rw [quotient_one, deriv_norm_at_zero]
  norm_num

private theorem quotient_three_lt_threshold :
    ‖orderedPoly aa ((0:ℂ),(0:ℂ)) - orderedPoly aa ((3:ℂ),(3/2:ℂ))‖ /
      ‖((0:ℂ),(0:ℂ)) - ((3:ℂ),(3/2:ℂ))‖ <
      ‖orderedDeriv aa ((0:ℂ),(0:ℂ))‖ / (3 : ℝ) := by
  rw [quotient_three, deriv_norm_at_zero]
  norm_num

theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨w, hw, hineq⟩ :=
    hclaim (ℂ × ℂ) 3 (by norm_num) aa ((0:ℂ),(0:ℂ)) deriv_at_zero_ne
  rcases (critical_set w).mp hw with h1 | h3
  · rw [h1] at hineq
    exact (not_lt_of_ge hineq) quotient_one_lt_threshold
  · rw [h3] at hineq
    exact (not_lt_of_ge hineq) quotient_three_lt_threshold

end D5.S3.Quantum.Algebra.CStarDualMeanValue
