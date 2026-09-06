/- GID: D5/S3/Arith/CentralBellCubicRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/CentralBellCubicRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=atom:cea8eba5ad5ecc076ed36d846fc5b0bc88b60c7dc329fe8ab87bd21fcc5b7f3d; result=D5/S3/Arith/CentralBellCubicRefutation.conjecture3_refuted
   digest: Rational double roots refute both printed central Bell cubic distinctness claims. -/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Coeff

namespace D5.S3.Arith.CentralBellCubicRefutation

noncomputable section

/-- The printed n = 3, lambda = 3 Euler-type cosine cubic, in expanded form.
Khan et al., DOI 10.3934/nhm.2026030, supply the conjecture being refuted. -/
def eulerCubic (x y z : Complex) : Complex :=
  -(9 * x / 4) + x ^ 3 - 3 * x * y ^ 2 - 2 * z +
    3 * x ^ 2 * z - 3 * y ^ 2 * z + 3 * x * z ^ 2 + z ^ 3

/-- The printed n = 3, lambda = 3 Bernoulli-type cosine cubic, in expanded form.
Khan et al., DOI 10.3934/nhm.2026030, supply the conjecture being refuted. -/
def bernoulliCubic (x y z : Complex) : Complex :=
  -(3 * x / 4) + x ^ 3 - 3 * x * y ^ 2 - z / 2 +
    3 * x ^ 2 * z - 3 * y ^ 2 * z + 3 * x * z ^ 2 + z ^ 3

/-- Existence of three pairwise distinct complex zeros. -/
def HasThreeDistinctRoots (f : Complex -> Complex) : Prop :=
  exists a b c : Complex,
    f a = 0 ∧ f b = 0 ∧ f c = 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c

-- Finite jets only: the identification with the infinite generating functions
-- is source interpretation, not a formal analytic theorem of this module.
open Polynomial in
def egfJet (q x y z : Complex) : Polynomial Complex :=
  (1 - C q * X ^ 2) *
    (1 + C x * X + C (x ^ 2 / 2) * X ^ 2 + C (x ^ 3 / 6) * X ^ 3) *
    (1 - C (y ^ 2 / 2) * X ^ 2) *
    (1 + C z * X + C (z ^ 2 / 2) * X ^ 2 + C (z ^ 3 / 6 + z / 24) * X ^ 3)

private theorem egfJet_coeff_three (q x y z : Complex) :
    6 * (egfJet q x y z).coeff 3 =
      (x + z) ^ 3 - 3 * (x + z) * y ^ 2 - 6 * q * (x + z) + z / 4 := by
  simp [egfJet, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Polynomial.coeff_one, Polynomial.coeff_X]
  ring

theorem euler_egf_coefficient (x y z : Complex) :
    6 * (egfJet (3 / 8) x y z).coeff 3 = eulerCubic x y z := by
  rw [egfJet_coeff_three]
  unfold eulerCubic
  ring

theorem bernoulli_egf_coefficient (x y z : Complex) :
    6 * (egfJet (1 / 8) x y z).coeff 3 = bernoulliCubic x y z := by
  rw [egfJet_coeff_three]
  unfold bernoulliCubic
  ring

theorem euler_coefficient_bridge (x y z : Complex) :
    eulerCubic x y z = (x + z) ^ 3 - 3 * (x + z) * (y ^ 2 + 3 / 4) + z / 4 := by
  rw [← euler_egf_coefficient, egfJet_coeff_three]
  ring

theorem bernoulli_coefficient_bridge (x y z : Complex) :
    bernoulliCubic x y z = (x + z) ^ 3 - 3 * (x + z) * (y ^ 2 + 1 / 4) + z / 4 := by
  rw [← bernoulli_egf_coefficient, egfJet_coeff_three]
  ring

theorem euler_factorization (x : Complex) :
    eulerCubic x (1 / 2) 8 = (x + 7) ^ 2 * (x + 10) := by
  rw [euler_coefficient_bridge]
  ring

theorem bernoulli_factorization (x : Complex) :
    bernoulliCubic x (2 / 3) (125 / 27) = (x + 205 / 54) ^ 2 * (x + 170 / 27) := by
  rw [bernoulli_coefficient_bridge]
  ring

/-- Exact rational parameter identities for the Bernoulli double-root certificate. -/
theorem bernoulli_parameter_identities :
    (2 / 3 : Rat) ^ 2 + 1 / 4 = (5 / 6) ^ 2 ∧
    (125 / 27 : Rat) / 4 = 2 * (5 / 6) ^ 3 := by
  norm_num

private theorem euler_roots (x : Complex) :
    eulerCubic x (1 / 2) 8 = 0 ↔ x = -7 ∨ x = -10 := by
  rw [euler_factorization, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0)]
  simp only [add_eq_zero_iff_eq_neg]

private theorem bernoulli_roots (x : Complex) :
    bernoulliCubic x (2 / 3) (125 / 27) = 0 ↔ x = -(205 / 54) ∨ x = -(170 / 27) := by
  rw [bernoulli_factorization, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0)]
  simp only [add_eq_zero_iff_eq_neg]

private theorem no_three_of_two (f : Complex -> Complex) (r s : Complex)
    (h : forall x, f x = 0 ↔ x = r ∨ x = s) :
    ¬ HasThreeDistinctRoots f := by
  rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  rcases (h a).mp ha with ha | ha <;>
    rcases (h b).mp hb with hb | hb <;>
    rcases (h c).mp hc with hc | hc <;> simp_all

/-- Rational parameters refute Conjecture 3 for the printed n = 3, lambda = 3
Euler cubic: its complete complex root set has exactly two elements. This also
refutes any universal-lambda reading that includes lambda = 3. -/
theorem conjecture3_refuted :
    (∃ y z : Rat, y = 1 / 2 ∧ z = 8 ∧
      (∀ x : Complex,
        eulerCubic x ((y : Real) : Complex) ((z : Real) : Complex) = 0 ↔
          x = -7 ∨ x = -10) ∧
      ¬ HasThreeDistinctRoots
        (fun x => eulerCubic x ((y : Real) : Complex) ((z : Real) : Complex))) ∧
    (-7 : Complex) ≠ -10 ∧
    ¬ (∀ y z : Real,
      HasThreeDistinctRoots (fun x => eulerCubic x (y : Complex) (z : Complex))) := by
  have hno := no_three_of_two (fun x => eulerCubic x (1 / 2) 8) (-7) (-10) euler_roots
  refine ⟨?_, by norm_num, ?_⟩
  · refine ⟨1 / 2, 8, rfl, rfl, ?_, ?_⟩
    · simpa using euler_roots
    · simpa using hno
  · intro h
    apply hno
    simpa using h (1 / 2) 8

/-- Rational parameters refute Conjecture 1 for the printed n = 3, lambda = 3
Bernoulli cubic: its complete complex root set has exactly two elements. This
also refutes any universal-lambda reading that includes lambda = 3. -/
theorem conjecture1_refuted :
    (∃ y z : Rat, y = 2 / 3 ∧ z = 125 / 27 ∧
      (∀ x : Complex,
        bernoulliCubic x ((y : Real) : Complex) ((z : Real) : Complex) = 0 ↔
          x = -(205 / 54) ∨ x = -(170 / 27)) ∧
      ¬ HasThreeDistinctRoots
        (fun x => bernoulliCubic x ((y : Real) : Complex) ((z : Real) : Complex))) ∧
    (-(205 / 54) : Complex) ≠ -(170 / 27) ∧
    ¬ (∀ y z : Real,
      HasThreeDistinctRoots (fun x => bernoulliCubic x (y : Complex) (z : Complex))) := by
  have hno := no_three_of_two (fun x => bernoulliCubic x (2 / 3) (125 / 27))
    (-(205 / 54)) (-(170 / 27)) bernoulli_roots
  refine ⟨?_, by norm_num, ?_⟩
  · refine ⟨2 / 3, 125 / 27, rfl, rfl, ?_, ?_⟩
    · simpa using bernoulli_roots
    · simpa using hno
  · intro h
    apply hno
    simpa using h (2 / 3) (125 / 27)

example : Nonempty Complex := ⟨0⟩
example : Nonempty Real := ⟨0⟩
example : ∃ y z : Rat, y = 1 / 2 ∧ z = 8 := ⟨1 / 2, 8, rfl, rfl⟩
example : ∃ y z : Rat, y = 2 / 3 ∧ z = 125 / 27 := ⟨2 / 3, 125 / 27, rfl, rfl⟩
example : eulerCubic 0 0 1 = -1 := by norm_num [eulerCubic]
example : bernoulliCubic 0 0 1 = 1 / 2 := by norm_num [bernoulliCubic]
example : eulerCubic (-7) (1 / 2) 8 = 0 := (euler_roots _).mpr (Or.inl rfl)
example : eulerCubic (-10) (1 / 2) 8 = 0 := (euler_roots _).mpr (Or.inr rfl)
example : bernoulliCubic (-(205 / 54)) (2 / 3) (125 / 27) = 0 :=
  (bernoulli_roots _).mpr (Or.inl rfl)
example : bernoulliCubic (-(170 / 27)) (2 / 3) (125 / 27) = 0 :=
  (bernoulli_roots _).mpr (Or.inr rfl)

#print axioms eulerCubic
#print axioms bernoulliCubic
#print axioms HasThreeDistinctRoots
#print axioms conjecture3_refuted
#print axioms conjecture1_refuted

end

end D5.S3.Arith.CentralBellCubicRefutation
