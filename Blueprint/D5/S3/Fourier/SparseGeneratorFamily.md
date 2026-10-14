# Sparse Generator Family

## Abstract

Uniform cyclic samples produce symmetric sparse generating sets with a positive ordinary spectral gap.

**Theorem 1.1 (Character orthogonality at every cyclic frequency).**

Lean statement: `D5/S3/Fourier/SparseGeneratorFamily.char_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/SparseGeneratorFamily.char_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of the standard cyclic character at frequency a is N when a=0 and zero otherwise. Nonunit frequencies and composite cyclic orders remain in scope.

**Theorem 1.2 (A lower logarithmic scale).**

Lean statement: `D5/S3/Fourier/SparseGeneratorFamily.large_log`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/SparseGeneratorFamily.large_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain N>=ceil(exp(128)) implies log(N)>=128. This controls the sampling and graph-radius estimates.

**Theorem 1.3 (Positive cyclic order).**

Lean statement: `D5/S3/Fourier/SparseGeneratorFamily.large_order_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/SparseGeneratorFamily.large_order_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same domain implies N>0, supplying the nonzero-order instance in the obstruction and its translation-dependent realization.

**Theorem 1.4 (Sampling and radius bounds).**

Lean statement: `D5/S3/Fourier/SparseGeneratorFamily.parameters_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/SparseGeneratorFamily.parameters_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For L=log(N), q=ceil(16L) and r=floor(L/16), one has 16L<=q, q+1<=17L, r>=8 and L/32<=r<=L/16.

**Theorem 1.5 (Calibration tolerance).**

Lean statement: `D5/S3/Fourier/SparseGeneratorFamily.tolerance_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/SparseGeneratorFamily.tolerance_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation tolerance pi/(2r) is positive and at most pi/16, which is strictly below 1/4. These bounds apply to the complete generator rows.

**Theorem 1.6 (Commutative walk volume).**

Lean statement: `D5/S3/Fourier/SparseGeneratorFamily.volume_numeric_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/SparseGeneratorFamily.volume_numeric_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural p<=34log(N), choose(p+r,r)<=sqrt(N). A weighted binomial term bounds this volume; it controls the support of the graph-distance phase.

**Theorem 1.7 (Symmetric sparse families at every large order).**

Lean statement: `D5/S3/Fourier/SparseGeneratorFamily.familySet_good`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/SparseGeneratorFamily.familySet_good` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed choice familySet(N) excludes zero, is symmetric under negation, has cardinality 2ceil(16log(N)), and has ordinary squared-character-chord gap at least one. Uniform independent samples exclude signed collisions and two-torsion while controlling every nonzero frequency.

**Theorem 1.8 (Positive gap forces generation).**

Lean statement: `D5/S3/Fourier/SparseGeneratorFamily.gap_generating`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/SparseGeneratorFamily.gap_generating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any cyclic Finset S, a positive ordinary gap forces its additive subgroup closure to be the full cyclic group. An annihilating frequency would have zero chord average; the finite annihilator cardinality identity then forces generation.

## References

- Truth anchor: `D5/S3/Fourier/SparseGeneratorFamily.char_sum`
- Truth anchor: `D5/S3/Fourier/SparseGeneratorFamily.familySet_good`
- Truth anchor: `D5/S3/Fourier/SparseGeneratorFamily.gap_generating`
- Truth anchor: `D5/S3/Fourier/SparseGeneratorFamily.large_log`
- Truth anchor: `D5/S3/Fourier/SparseGeneratorFamily.large_order_pos`
- Truth anchor: `D5/S3/Fourier/SparseGeneratorFamily.parameters_bounds`
- Truth anchor: `D5/S3/Fourier/SparseGeneratorFamily.tolerance_bounds`
- Truth anchor: `D5/S3/Fourier/SparseGeneratorFamily.volume_numeric_bound`
- Dependency: [D5/S3/Fourier/FinitePoisson](FinitePoisson.md)
- Dependency: [D5/S3/Fourier/GeneratorRowStability](GeneratorRowStability.md)
