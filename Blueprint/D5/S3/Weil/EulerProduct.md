# Euler Windows and Single-Address Heat

## Abstract

Finite Euler windows and single-address weights connect the prime and zero sides.

**Theorem 1.1 (Finite Euler windows have only the local denominator lattice).**

$$\forall S\subset_{\operatorname{fin}}\mathbb{N},\ (\forall p\in S,\operatorname{Prime}(p)) \Rightarrow \forall s\in\mathbb{C},\ (\operatorname{finiteEulerProduct}(S,s)\neq 0 \Leftrightarrow \operatorname{FiniteEulerRegular}(S,s)) \land (\neg\operatorname{FiniteEulerRegular}(S,s) \Leftrightarrow \exists p\in S,\exists k\in\mathbb{Z},\ s=\frac{2\pi i k}{\log p})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus` (`✓ std3`). ∎

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

A finite Euler product is nonzero exactly on the locus where every local denominator is nonzero, and the complementary denominator-zero locus is the union of the imaginary lattices indexed by its primes. Lean totalizes inversion with zero inverse equal to zero, so the zero-free clause is deliberately restricted to the regular locus; no pole order or numerical window certificate is asserted.

**Definition 1.2 (The single-address reading is the von Mangoldt weight).**

$(\forall p, k,\ \operatorname{Prime}(p) \land k\neq0 \Rightarrow \operatorname{singleAddressReading}(p^k)=\log p) \land (\forall n,\ \neg\operatorname{IsPrimePow}(n) \Rightarrow \operatorname{singleAddressReading}(n)=0)$

*Formalization.* `D5/S3/Weil/EulerProduct.single_address_reading_spec` (`✓ std3`).

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

Under the value map from a one-prime ledger state to a natural prime power, a nonzero exponent at p reads log p, while every non-prime-power value reads zero. This is the classical von Mangoldt coefficient in the repository's single-address coordinates.

**Proposition 1.3 (The logarithmic derivative is the single-address heat trace).**

$\forall s\in\mathbb{C},\ 1<\Re(s) \Rightarrow \operatorname{singleAddressHeatTrace}(s)=-\frac{\operatorname{deriv}(\operatorname{classicalZeta})(s)}{\operatorname{classicalZeta}(s)}$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/EulerProduct.single_address_heat_trace_eq_log_derivative` (`✓ std3`). ∎

*Citation.* Tom M. Apostol (1976). *Introduction to Analytic Number Theory*. DOI: [10.1007/978-1-4757-5579-4](https://doi.org/10.1007/978-1-4757-5579-4).

*Commentary.*

In the convergence half-plane with real part greater than one, the L-series of the single-address reading equals minus the derivative of the classical zeta function divided by the zeta function. The statement adds no continuation beyond that half-plane.

**Remark 1.4 (Journal and ledger readings).**

Lean statement: `D5/S3/Weil/EulerProduct.single_address_reading_spec`

*Formalization.* `D5/S3/Weil/EulerProduct.single_address_reading_spec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ordering terms by generated value resembles a chronological journal, while grouping powers by prime address resembles a classified ledger. The single-address theorem supplies the local weight behind that analogy; it does not formalize heat-time cosmology or a theta functional equation.

**Remark 1.5 (Finite Euler windows do not create global zeros).**

Lean statement: `D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus`

*Formalization.* `D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every regular finite Euler window is nonzero, so no finite set of local factors realizes a nontrivial global zero. This supports only a finite-versus-tail boundary; collective-mode, prime-deletion, dense-phase, and equal-loudness interpretations are not proved here.

## References

- Truth anchor: `D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus`
- Truth anchor: `D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus`
- Truth anchor: `D5/S3/Weil/EulerProduct.single_address_heat_trace_eq_log_derivative`
- Truth anchor: `D5/S3/Weil/EulerProduct.single_address_reading_spec`
- Truth anchor: `D5/S3/Weil/EulerProduct.single_address_reading_spec`
