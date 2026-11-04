# QuadraticImaginaryInvariants

## Abstract

The negative discriminant excludes real embeddings. The field has one complex place and unit rank zero. The regulator is its zero-dimensional determinant and the two actual torsion units give the residue pi times the genuine ideal class number divided by sqrt(p).

The negative discriminant excludes real embeddings. The field has one complex place and unit rank zero. The regulator is its zero-dimensional determinant and the two actual torsion units give the residue pi times the genuine ideal class number divided by sqrt(p).

Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.

**Theorem 1.1 (complexPlaces).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.complexPlaces`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.complexPlaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The exact Lean declaration D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary.complexPlaces supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration.

**Theorem 1.2 (unitRank).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.unitRank`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.unitRank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The exact Lean declaration D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary.unitRank supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration.

**Theorem 1.3 (field_regulator).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.field_regulator`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.field_regulator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

A real embedding would give a real square equal to the negative integer minus p. -/ instance totallyComplex : NumberField.IsTotallyComplex (Field p) where isComplex w := by rw [← not_isReal_iff_isComplex] intro hw let φ := embedding_of_isReal hw let ω : Field p := QuadraticAlgebra.omega have hω : ω * ω = (orderA p : Field p) + ω := by simpa [ω, Algebra.smul_def] using (QuadraticAlgebra.omega_mul_omega_eq_add (a := (orderA p : ℚ)) (b := (1 : ℚ))) have heq := congrArg φ hω simp only [map_mul, map_add, map_intCast] at heq have hD : (1 : ℝ) + 4 * (orderA p : ℝ) = -(p : ℝ) := by exact_mod_cast (show 1 + 4 * orderA p = -(p : ℤ) by simpa only [QuadraticAlgebra.discr_def, one_pow] using order_discr p) have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos nlinarith [sq_nonneg (2 * φ ω - 1)] theorem complexPlaces : nrComplexPlaces (Field p) = 1 := by have h := NumberField.IsTotallyComplex.finrank (Field p) rw [QuadraticAlgebra.finrank_eq_two] at h omega theorem unitRank : NumberField.Units.rank (Field p) = 0 := by rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero, complexPlaces] /-- The regulator is the determinant in dimension zero, with the Mathlib normalization.

**Theorem 1.4 (field_torsionOrder).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.field_torsionOrder`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.field_torsionOrder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The actual maximal order has exactly two torsion units once p greater than three.

**Theorem 1.5 (zeta_residue).**

Lean statement: `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.zeta_residue`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.zeta_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Specialization of the genuine number-field residue expression, retaining the actual cardinality of the maximal-order ideal class group. This is field data, not yet the quadratic Dedekind-zeta/Dirichlet-L identification.

## References

- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.complexPlaces`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.field_regulator`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.field_torsionOrder`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.unitRank`
- Truth anchor: `D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants.zeta_residue`
- Dependency: [D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal](QuadraticOrderMaximal.md)
