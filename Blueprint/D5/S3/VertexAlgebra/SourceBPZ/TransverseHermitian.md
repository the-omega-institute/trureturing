# Original Transverse Hermitian Norm

## Abstract

Exact original transverse BPZ/Hermitian positivity on the integral charge and oscillator carrier.

The form is canonical OriginalMatterHermitian.Hm x y = sourcePairing D (theta D (kappaCarrier x)) y. The source pairing, reflection, conjugation, original integral charges and oscillator carrier are unchanged. RealOrthonormalFrame is a local real orthonormal positive subspace hypothesis of the original possibly indefinite integral Gram; there is no whole-Gram positivity, rank-26 or nonzero-charge assumption.

The exact norm is the finite sum over charges a and occupation vectors alpha of the product over colour/mode pairs (j,r) of alpha(j,r)! times (r+1)^alpha(j,r), multiplied by normSq of the coefficient of x(a). No half-frequency, occupation factorial, phase conjugation or charge row is omitted. Original Wick contraction and theta signs are proved to cancel before the comparison with the independently defined factorial form.

This is classical symmetric/Bargmann Fock normalization applied to the repository's original source form, with no literature novelty claim. The reused native factorial and current substitution results retain their original provenance and licenses. The finite-support polynomial identity proves positivity on the transverse image only; it supplies no analytic completion, positivity on the whole indefinite carrier, p0 BRST cohomology or full no-ghost theorem. The full Monster/VOA/CFT/anomaly/fusion/BRST/string/AdS programme remains unfinished.

The six public theorem registrations remain OPEN: the source-owner Reg mirror, exact source selection/reconstruction, lawful realization bridge and readout law, whole-family variation and sensitivity, and observational dependence have not been supplied. No declared_validated status is claimed. The linked-issue disclosure is https://github.com/the-omega-institute/trureturing/issues/25831.

**Definition 1.1 (Original coordinate space).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.E`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite coordinate space is Fin D.rank to complex numbers.

**Definition 1.2 (Original bilinear Gram form).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.originalG`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.originalG` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Uses the original integral Gram matrix with no global positivity hypothesis.

**Definition 1.3 (Real orthonormal transverse frame).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.RealOrthonormalFrame`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.RealOrthonormalFrame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A frame has real complex coordinates and its bilinear Gram matrix is the identity; t and the original lattice rank may be zero.

**Definition 1.4 (Transverse polynomials).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Polynomial`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Polynomials have variables indexed by transverse colour and every natural mode.

**Definition 1.5 (Finite occupation indices).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Occupation`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Occupation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An occupation is a finitely supported natural exponent vector on all transverse modes.

**Definition 1.6 (Original linear oscillator).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.lin`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.lin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Maps a transverse generator into the genuine linear combination of original oscillator variables at the same mode.

**Definition 1.7 (Original polynomial embedding).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.phi`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Extends the frame linear combinations by the native free polynomial algebra homomorphism.

**Definition 1.8 (Original directional annihilation).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.annihilateAlong`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.annihilateAlong` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A derivation formed from the existing original Gram-weighted annihilation derivations.

**Theorem 1.9 (Transverse chain rule).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.annihilateAlong_phi`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.annihilateAlong_phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every polynomial, original directional annihilation of the frame substitution equals substitution of the transverse partial derivative. The generator calculation uses frame Gram orthonormality, and Leibniz extends it.

**Definition 1.10 (Literal reflected conjugate Wick form).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.bpzOsc`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.bpzOsc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Applies the existing integerWick to sigma of canonical kappaOsc of phi in the first slot, and phi in the second. This definition does not mention a positive target form.

**Definition 1.11 (Integer frequency square root).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.frequencyScale`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.frequencyScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scale is the real square root of r+1, cast to complex numbers, for every natural r.

**Definition 1.12 (Invertible frequency substitution).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.rescale`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.rescale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reuses OriginalCurrentMetric.substitutionEquiv with the derived diagonal frequency matrix and its two-sided inverse. It scales each mode-r generator by sqrt(r+1).

**Theorem 1.13 (Original Wick to factorial comparison).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.bpzOsc_eq_target`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.bpzOsc_eq_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal reflected conjugate original Wick form equals FactorialFockMetric.inner after frequency rescaling, for every pair of transverse polynomials. Real frame coordinates give conjugation compatibility; theta contributes the sign which cancels the signed Wick contraction, leaving frequency r+1. The comparison follows from the original creation recurrence and the factorial creation/partial-derivative law.

**Definition 1.14 (Single original charge embedding).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.delta`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retains any original integral charge and substitutes its transverse polynomial into the original oscillator.

**Theorem 1.15 (Exact charge delta and factorial form).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.source_delta_delta_eq_factorial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.source_delta_delta_eq_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any original integral charges a and b, including zero, canonical Hm of the embedded states equals the rescaled factorial inner product when a=b and zero otherwise. The charge equality follows from the original opposite-charge sourcePairing and literal theta reflection.

**Definition 1.16 (Finite original charge embedding).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.transverseEmbed`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.transverseEmbed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Maps each component of the original finite charge support by phi, with no charge quotient, cutoff or suppressed frequency.

**Definition 1.17 (Occupation frequency product).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.frequencyWeight`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.frequencyWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight is the product of (r+1) to the occupation of each colour/mode variable, including the empty product.

**Definition 1.18 (Exact factorial and frequency weight).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.exactWeight`

*Formalization.* `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.exactWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplies FactorialFockMetric.weight, the product of occupation factorials, by frequencyWeight. Every such natural weight is strictly positive.

**Theorem 1.19 (Exact rescaled coefficient norm).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.rescaled_inner_coeff_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.rescaled_inner_coeff_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every transverse polynomial P, the factorial self-pairing after rescale is the finite sum of exactWeight times normSq of each original coefficient. The proof computes the actual rescaled monomials and their coefficients; sqrt(r+1) squared supplies exactly the frequency product.

**Theorem 1.20 (Original finite-charge coefficient norm).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Hm_self_eq_exact_finite_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Hm_self_eq_exact_finite_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finitely supported original charge family x, canonical Hm of its transverse embedding with itself equals the sum over x.support and each polynomial support of exactWeight times coefficient normSq. All original charge rows, including zero, are retained.

**Theorem 1.21 (Strict positivity on the original transverse image).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Hm_self_strict_positive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Hm_self_strict_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero finite-charge transverse polynomial family, the literal original embedded Hm self-pairing has imaginary part zero and strictly positive real part. A nonzero charge component and a nonzero polynomial coefficient supply a strictly positive term in the exact finite sum.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.E`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Hm_self_eq_exact_finite_sum`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Hm_self_strict_positive`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Occupation`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.Polynomial`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.RealOrthonormalFrame`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.annihilateAlong`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.annihilateAlong_phi`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.bpzOsc`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.bpzOsc_eq_target`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.delta`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.exactWeight`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.frequencyScale`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.frequencyWeight`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.lin`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.originalG`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.phi`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.rescale`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.rescaled_inner_coeff_sum`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.source_delta_delta_eq_factorial`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian.transverseEmbed`
- Dependency: [D5/S3/VertexAlgebra/FactorialFockMetric](../FactorialFockMetric.md)
- Dependency: [D5/S3/VertexAlgebra/OriginalCurrentMetric](../OriginalCurrentMetric.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian](OriginalMatterHermitian.md)
