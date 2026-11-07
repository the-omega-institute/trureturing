/- GID: D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [occil2026bernreq]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.claim; result=D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.result; claim=D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.claim
   digest: Both original convex Bernstein correction prescriptions have a negative normalized coefficient. -/

import D5.S3.Observer.BlockStructure.CommonDenominatorPolynomialBasis
import Mathlib.Tactic

open Polynomial Finset
noncomputable section
namespace D5.S3.Analytic.SeriesInequalities.OccilBernsteinCorrectionRefutation

def f (x : ℝ) : ℝ := x ^ 2 - x + 1/2

def B (n : ℕ) (u : ℝ → ℝ) : ℝ[X] :=
  ∑ j ∈ range (n+1), C (u ((j : ℝ) / n)) * bernsteinPolynomial ℝ n j

def admissible (u : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc (0:ℝ) 1, 0 < u x ∧ u x ≤ 1) ∧
  (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    ∀ t ∈ Set.Icc (0:ℝ) 1, u (t*x+(1-t)*y) ≤ t*u x+(1-t)*u y)

def maxError (u : ℝ → ℝ) (n : ℕ) (M : ℝ) : Prop :=
  (∀ x ∈ Set.Icc (0:ℝ) 1, |(B n u).eval x-u x| ≤ M) ∧
  ∃ x ∈ Set.Icc (0:ℝ) 1, |(B n u).eval x-u x| = M

def midpointError (u : ℝ → ℝ) (n : ℕ) : ℝ :=
  |(B n u).eval (1/2)-u (1/2)|

def coeff : Fin 5 → ℝ := ![1/16, 0, -1/48, 0, 1/16]

private theorem f_admissible : admissible f := by
  constructor
  · intro x hx
    constructor
    · dsimp [f]; nlinarith [sq_nonneg (x-1/2)]
    · dsimp [f]; nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  · intro x hx y hy t ht
    have h := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (x-y))
    have he : t*f x+(1-t)*f y-f (t*x+(1-t)*y) = t*(1-t)*(x-y)^2 := by
      dsimp [f]; ring
    linarith

private theorem f_symmetric (x : ℝ) : f (1-x)=f x := by dsimp [f]; ring

private theorem B_two : B 2 f = C (1/2) * (X^2-X) + C (1/2) := by
  apply Polynomial.funext
  intro x
  norm_num [B, f, Finset.sum_range_succ, bernsteinPolynomial, Nat.choose, eval_finsetSum]
  <;> ring

private theorem B_four : B 4 f = C (3/4) * (X^2-X) + C (1/2) := by
  apply Polynomial.funext
  intro x
  norm_num [B, f, Finset.sum_range_succ, bernsteinPolynomial, Nat.choose, eval_finsetSum]
  <;> ring

private theorem error_two (x : ℝ) : (B 2 f).eval x-f x = x*(1-x)/2 := by
  rw [B_two]; simp [f]; ring

private theorem error_four (x : ℝ) : (B 4 f).eval x-f x = x*(1-x)/4 := by
  rw [B_four]; simp [f]; ring

private theorem max_two : maxError f 2 (1/8) := by
  constructor
  · intro x hx
    rw [error_two, abs_of_nonneg (div_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) (by norm_num))]
    nlinarith [sq_nonneg (x-1/2)]
  · refine ⟨1/2, by norm_num, ?_⟩
    rw [error_two]; norm_num

private theorem max_four : maxError f 4 (1/16) := by
  constructor
  · intro x hx
    rw [error_four, abs_of_nonneg (div_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) (by norm_num))]
    nlinarith [sq_nonneg (x-1/2)]
  · refine ⟨1/2, by norm_num, ?_⟩
    rw [error_four]; norm_num

private theorem mid_two : midpointError f 2 = 1/8 := by
  unfold midpointError; rw [error_two]; norm_num

private theorem mid_four : midpointError f 4 = 1/16 := by
  unfold midpointError; rw [error_four]; norm_num

private theorem representation : (B 4 f-C (1/16))-(B 2 f-C (1/8)) =
    ∑ j : Fin 5, C (coeff j) * bernsteinPolynomial ℝ 4 j := by
  rw [B_four, B_two]
  apply Polynomial.funext
  intro x
  norm_num [coeff, Fin.sum_univ_succ, bernsteinPolynomial, Nat.choose, eval_finsetSum]
  <;> ring

private theorem negative : coeff 2 < 0 := by norm_num [coeff]

/-- Normalized Bernstein realization at the specified representation degree. -/
def realization (d : ℕ) (a : Fin (d+1) → ℝ) : ℝ[X] :=
  ∑ j : Fin (d+1), C (a j) * bernsteinPolynomial ℝ d j

/-- Nonnegativity in the normalized basis at this exact representation degree. -/
def nonnegativeCoefficients (d : ℕ) (p : ℝ[X]) : Prop :=
  ∃ a : Fin (d+1) → ℝ, p = realization d a ∧ ∀ j, 0 ≤ a j

/-- The original attained-maximum correction assertion, without a continuity premise. -/
def maximumBranch : Prop :=
  ∀ u : ℝ → ℝ, admissible u → ∀ k : ℕ, 1 ≤ k →
  ∀ M N : ℝ, maxError u (2^k) M → maxError u (2*(2^k)) N →
  nonnegativeCoefficients (2*(2^k))
    ((B (2*(2^k)) u-C N)-(B (2^k) u-C M))

/-- The original symmetric midpoint-error assertion, with no maximum premise. -/
def midpointBranch : Prop :=
  ∀ u : ℝ → ℝ, admissible u →
  (∀ x ∈ Set.Icc (0:ℝ) 1, u (1-x)=u x) → ∀ k : ℕ, 1 ≤ k →
  nonnegativeCoefficients (2*(2^k))
    ((B (2*(2^k)) u-C (midpointError u (2*(2^k))))-
      (B (2^k) u-C (midpointError u (2^k))))

/-- The unchanged conjunction registered for the original two prescriptions. -/
def claim : Prop := maximumBranch ∧ midpointBranch

private theorem realization_unique (d : ℕ) (a b : Fin (d+1) → ℝ)
    (h : realization d a = realization d b) : a = b := by
  have hc := congrArg (Polynomial.map Complex.ofRealHom) h
  have hs : (∑ j : Fin (d+1), (a j : ℂ) • bernsteinPolynomial ℂ d j) =
      ∑ j : Fin (d+1), (b j : ℂ) • bernsteinPolynomial ℂ d j := by
    simpa [realization, smul_eq_C_mul] using hc
  have hi := Fintype.linearIndependent_iffₛ.mp
    (D5.S3.Observer.BlockStructure.CommonDenominatorPolynomialBasis.bernstein_linearIndependent_complex d)
    (fun j => (a j : ℂ)) (fun j => (b j : ℂ)) hs
  funext j
  exact Complex.ofReal_injective (hi j)

private theorem increment_negative :
    ¬ nonnegativeCoefficients 4 ((B 4 f-C (1/16))-(B 2 f-C (1/8))) := by
  rintro ⟨a, ha, hpos⟩
  have he : realization 4 a = realization 4 coeff := ha.symm.trans representation
  have hu := realization_unique 4 a coeff he
  have hp := hpos (2 : Fin 5)
  rw [hu] at hp
  exact (not_le_of_gt negative) hp

private theorem branch_refutations : ¬ maximumBranch ∧ ¬ midpointBranch := by
  constructor
  · intro h
    have hp := h f f_admissible 1 (by norm_num) (1/8) (1/16) max_two max_four
    exact increment_negative (by simpa using hp)
  · intro h
    have hp := h f f_admissible (fun x _ => f_symmetric x) 1 (by norm_num)
    exact increment_negative (by simpa [mid_two, mid_four] using hp)

/-- The convex quadratic refutes both prescriptions and hence their conjunction. -/
theorem result : ¬ claim := by
  intro h
  exact branch_refutations.1 h.1

#check claim
#check result
#print axioms result
#check branch_refutations
#print axioms branch_refutations
end D5.S3.Analytic.SeriesInequalities.OccilBernsteinCorrectionRefutation
