/- GID: D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants
   generality: G
   mirror-B: D5/B/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signature, torsion, regulator and actual zeta residue of prime imaginary quadratic fields. -/

import D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.DedekindZeta

namespace D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary

open NumberField NumberField.InfinitePlace
open scoped Real

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- A real embedding would give a real square equal to the negative integer minus p. -/
instance totallyComplex : NumberField.IsTotallyComplex (Field p) where
  isComplex w := by
    rw [← not_isReal_iff_isComplex]
    intro hw
    let φ := embedding_of_isReal hw
    let ω : Field p := QuadraticAlgebra.omega
    have hω : ω * ω = (orderA p : Field p) + ω := by
      simpa [ω, Algebra.smul_def] using
        (QuadraticAlgebra.omega_mul_omega_eq_add (a := (orderA p : ℚ)) (b := (1 : ℚ)))
    have heq := congrArg φ hω
    simp only [map_mul, map_add, map_intCast] at heq
    have hD : (1 : ℝ) + 4 * (orderA p : ℝ) = -(p : ℝ) := by
      exact_mod_cast (show 1 + 4 * orderA p = -(p : ℤ) by
        simpa only [QuadraticAlgebra.discr_def, one_pow] using order_discr p)
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    nlinarith [sq_nonneg (2 * φ ω - 1)]

theorem complexPlaces : nrComplexPlaces (Field p) = 1 := by
  have h := NumberField.IsTotallyComplex.finrank (Field p)
  rw [QuadraticAlgebra.finrank_eq_two] at h
  omega

theorem unitRank : NumberField.Units.rank (Field p) = 0 := by
  rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero, complexPlaces]

/-- The regulator is the determinant in dimension zero, with the Mathlib normalization. -/
theorem field_regulator : NumberField.Units.regulator (Field p) = 1 := by
  classical
  have hc := Fintype.card_congr (NumberField.Units.equivFinRank (Field p))
  rw [Fintype.card_fin, unitRank] at hc
  letI : IsEmpty {v : InfinitePlace (Field p) //
      v ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
    Fintype.card_eq_zero_iff.mp hc.symm
  rw [NumberField.Units.regulator_eq_det' (Field p)]
  simp

/-- The actual maximal order has exactly two torsion units once p greater than three. -/
theorem field_torsionOrder (hp : 3 < p) : NumberField.Units.torsionOrder (Field p) = 2 := by
  classical
  letI := Fintype.ofFinite (NumberField.Units.torsion (Field p))
  rw [NumberField.Units.torsionOrder, Nat.card_eq_fintype_card]
  apply Finset.card_eq_two.mpr
  refine ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x => ⟨fun _ => ?_, fun _ => Finset.mem_univ _⟩⟩
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  rcases integral_unit_eq_one_or_neg_one p hp x.1 with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

/-- Specialization of the genuine number-field residue expression, retaining the actual
cardinality of the maximal-order ideal class group. This is field data, not yet the
quadratic Dedekind-zeta/Dirichlet-L identification. -/
theorem zeta_residue (hp : 3 < p) :
    NumberField.dedekindZeta_residue (Field p) =
      Real.pi * (NumberField.classNumber (Field p) : ℝ) / Real.sqrt (p : ℝ) := by
  rw [NumberField.dedekindZeta_residue_def,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero, complexPlaces,
    field_regulator, field_torsionOrder p hp, field_discr]
  simp only [pow_zero, pow_one, one_mul, mul_one, Int.cast_neg, Int.cast_natCast,
    abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ (p : ℝ) from Nat.cast_nonneg p), Nat.cast_ofNat]
  ring

end D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary
