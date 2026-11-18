# Finite reverse-test attainment

## Abstract

A real finite maximal closed-perspective value for finite complex outputs has an actual finite reverse test attaining it, including infinite endpoint costs.

Let n be any finite type, A and B positive semidefinite complex n by n matrices, and f a real function convex on the strictly positive ray. No normalization, invertibility, operator convexity or finite endpoint hypothesis is imposed. The perspective uses the actual extended limits of f at zero and of f(x)/x at infinity, with value zero at the origin. The original value ranges over every sigma-finite source in an arbitrary independent universe and positive complex-linear trace-preserving preparation on its whole complex L1 space.

**Theorem 1.1 (Lower semicontinuity at infinite endpoints).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.curvatureRemainder_lowerSemicontinuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.curvatureRemainder_lowerSemicontinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such convex f, the actual curvatureRemainder hf p q is lower semicontinuous as an extended nonnegative function of the real pair (p,q). Each scalar hinge integrand is continuous in this pair and measurable in the positive threshold. Fatou's lemma for the neighborhood filter proves lower semicontinuity of each of the two curvature integrals. Their sum is lower semicontinuous. The statement includes both axes and the origin, with no finite-curvature or finite-cost restriction.

**Theorem 1.2 (A fixed affine contribution and a nonnegative objective).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.finiteCost_eq_affine_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.finiteCost_eq_affine_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual finite ReverseTest R preparing A and B, finiteCost hf R is affineMass f A B plus the EReal embedding of the finite sum of curvatureRemainder hf (R.p i) (R.q i). Taking traces of the actual preparation equations fixes the two sums of coefficients to Re Tr(A) and Re Tr(B). The affine contribution is therefore independent of the test. This is an extended-value equality and involves no subtraction of infinities.

**Definition 1.3 (A uniform finite alphabet).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.alphabetBound`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.alphabetBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

alphabetBound n is one plus the real dimension of the product of two full complex n by n matrix spaces and one real cost coordinate. This deliberately uses full matrix spaces, avoiding a Hermitian affine-dimension calculation. Only its uniform finiteness is needed for attainment; no sharp cardinality assertion is made.

**Theorem 1.4 (Exact finite-cost compression).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.finite_cost_compression`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.finite_cost_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite reverse test whose actual finiteCost is not positive infinity has a reverse test with at most alphabetBound n labels and exactly the same cost and prepared matrices. Finiteness of the nonnegative total remainder makes every individual remainder finite, so each actual cost term is represented by a real number. Apply finite-dimensional Caratheodory to the equally weighted average of the triples (p_i tau_i,q_i tau_i,c_i). Rescale the resulting coefficients by the old alphabet size and retain the selected original density states. The two matrix coordinates and the real cost coordinate are preserved exactly. An empty original alphabet is handled directly. Infinite costs are never converted to real numbers.

**Theorem 1.5 (An actual minimum on one fixed alphabet).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.fixed_alphabet_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.fixed_alphabet_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty output type and a fixed finite alphabet k, suppose the feasible coefficient-and-density set is nonempty. The coefficients lie between zero and the corresponding output trace, density matrices are positive semidefinite with trace one, and their two weighted sums equal exactly A and B. This set is compact: the coefficient intervals and density carrier are compact and the two continuous matrix-moment equations are closed constraints. The nonnegative sum of actual curvature remainders is lower semicontinuous, so it attains a minimum. Converting each matrix atom to the existing DensityState reconstructs an actual ReverseTest minimizing the original finiteCost over every test on that alphabet. The affine contribution is fixed. Infinite-cost boundary points and zero coefficients remain in the compact domain.

**Theorem 1.6 (Comparison with every finite alphabet).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.finite_attainment_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.finite_attainment_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite output type, if maximalValue hf A B is a real c, an actual ReverseTest with alphabetBound n labels has cost c. The real finite infimum supplies one finite-cost test. Exact compression and padding with zero coefficients make the fixed feasible alphabet nonempty. Its minimizer has cost at most every finite-cost test by compression; the inequality for an infinite-cost test is automatic. Conversely the fixed minimizer itself belongs to the full finite test class, giving the other infimum inequality. Neither an optimizer nor compactness of the finite-cost domain is assumed.

**Theorem 1.7 (Attainment of the original whole-complex-L1 value).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.original_finite_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.original_finite_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite complex PSD outputs A and B and every real f convex on the positive ray, if originalL1Value hf A B equals a real c, there exist a finite alphabet k and an actual repository ReverseTest A B k with finiteCost hf R=c. The original source universe is arbitrary and independent of the output universe. The proved sigma_finite_source_infimum_eq transfers the original value to the finite maximalValue before applying the fixed-alphabet argument. If Tr(A+B)=0, positivity forces A=B=0 and the empty reverse test attains zero. Every reverse test of the zero pair has zero coefficients by its trace equations. Empty output types are covered by this branch. Singular, unnormalized and zero pairs, and generators with either or both endpoint costs infinite, are all included.

Matsumoto, A new quantum version of f-divergence, arXiv:1311.4722v4, Theorem 9.4 (PDF p. 30), already proves finite-dimensional finite-value attainment under FC: f is proper, lower semicontinuous and convex, its domain contains (0,infinity), and f(0)=0 (PDF p. 4). The bounded finite-cardinality compression followed by compact minimization is his architecture, from Lemmas 4.1 and 9.2--9.3. Hiai, Mosonyi and Tomamichel, Hockey stick f-divergences, arXiv:2607.08760v1, Remark VII.4 (PDF p. 60) explicitly asks about general-convex minimal reverse-test existence, even in finite dimension; that question does not negate the earlier overlap.

The printed condition f(0)=0 alone is not a substantive novelty distinction. If the actual endpoint c=f(0+) is finite, taking the closed endpoint value and subtracting c subtracts the fixed constant c sigma(1), or c Tr(B) for matrix outputs, from every reverse-test cost and preserves minimizers. Transposition, hat f(t)=t f(1/t), and swapping the two inputs handle a finite opposite endpoint. The nonnegative-curvature formulation here also retains the range where both endpoints are infinite, using the established closed-perspective identity; the normalization observation does not establish priority for that remaining range. This result concerns finite-dimensional complex matrix outputs. It makes no assertion about arbitrary von Neumann algebras, a sharp alphabet bound, or worldwide priority.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.alphabetBound`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.curvatureRemainder_lowerSemicontinuous`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.finiteCost_eq_affine_remainder`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.finite_attainment_nonempty`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.finite_cost_compression`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.fixed_alphabet_minimum`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment.original_finite_attainment`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex](MaximalHockeyStickAllL1Convex.md)
