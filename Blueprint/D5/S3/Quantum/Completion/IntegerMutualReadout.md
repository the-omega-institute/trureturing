# Integer mutual-readout budgets

## Abstract

On an arbitrary raw complex kernel, universal finite Gaussian-integer mutual-readout budgets are equivalent to rational and complex budgets and Hermitian positive type.

**Definition 1.1 (The original finite comparison).**

$$\forall X: Type, \forall R: Type, [\operatorname{Zero}\left(R\right)], \forall e: R \to \mathbb{C}, \forall K: X \to X \to \mathbb{C}, \forall f: \operatorname{Finsupp}\left(X, R\right), \forall g: \operatorname{Finsupp}\left(X, R\right), \operatorname{readout}\left(e, K, f, g\right) = \sum_{x \in \operatorname{support}\left(f\right)} \sum_{y \in \operatorname{support}\left(g\right)} e(f(x))^{*} \operatorname{K}\left(x, y\right) e(g(y))$$

*Formalization.* `D5/S3/Quantum/Completion/IntegerMutualReadout.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any label type X, coefficient type R with zero, embedding e into the complex numbers and raw kernel K, readout is the finite double sum over the supports of f and g. The summand conjugates the first embedded coefficient and multiplies by the second without conjugation. No topology, norm, state, normalization or Hermitian condition on K is present.

**Definition 1.2 (The unrestricted finite-recipe budget).**

$$\forall X: Type, \forall R: Type, [\operatorname{Zero}\left(R\right)], \forall e: R \to \mathbb{C}, \forall K: X \to X \to \mathbb{C}, (\operatorname{Budget}\left(e, K\right) \Leftrightarrow \forall f: \operatorname{Finsupp}\left(X, R\right), \forall g: \operatorname{Finsupp}\left(X, R\right), 2 \operatorname{Re}\left(\operatorname{readout}\left(e, K, f, g\right)\right) \leq \operatorname{Re}\left(\operatorname{readout}\left(e, K, f, f\right)\right) + \operatorname{Re}\left(\operatorname{readout}\left(e, K, g, g\right)\right))$$

*Formalization.* `D5/S3/Quantum/Completion/IntegerMutualReadout.Budget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both recipes range over all finitely supported coefficient families on X. Supports have no common size bound and Gaussian-integer coefficients have no common magnitude bound; zero and empty recipes are retained. The three comparisons use the same K and the same scale.

**Definition 1.3 (Exact rational complex coordinates).**

$$\forall r: \mathbb{Q} \times \mathbb{Q}, \operatorname{rationalComplex}\left(r\right) = \operatorname{fst}\left(r\right) + \operatorname{snd}\left(r\right) i$$

*Formalization.* `D5/S3/Quantum/Completion/IntegerMutualReadout.rationalComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pair (a,b) denotes a+b i, with a and b rational. These are precisely Q(i)=Q+iQ; the pair is a coordinate presentation of the coefficient set, and is not assigned the componentwise product-ring multiplication. Each finite recipe uses these exact embedded complex values.

**Theorem 1.4 (All four conditions on the same raw kernel are equivalent).**

$$\forall X: Type, \forall K: X \to X \to \mathbb{C}, (\operatorname{Budget}\left(toComplex, K\right) \Leftrightarrow \operatorname{PosSemidef}\left(K\right)) \land (\operatorname{Budget}\left(rationalComplex, K\right) \Leftrightarrow \operatorname{PosSemidef}\left(K\right)) \land (\operatorname{Budget}\left(id, K\right) \Leftrightarrow \operatorname{PosSemidef}\left(K\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/IntegerMutualReadout.mutual_budget_iff_positive_type` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is C130 Theorem 2.3. X is arbitrary, including infinite and empty types, and K is any complex-valued table. Matrix.PosSemidef at this arbitrary index type asserts actual Hermitian symmetry of K and nonnegativity of every finitely supported complex quadratic form. Its existing submatrix theorem gives every finite indexed table, with arbitrary repeated labels and singular directions. Conversely, positivity of all finite tables recovers symmetry from two labels and each quadratic form from its finite support. Here toComplex denotes GaussianInt.toComplex. The equivalences each identify one of the integer, rational-coordinate and complex budgets with that same condition; no Hermitian premise is assumed.

For each fixed finite subset of labels, Matrix.den and Matrix.num_div_den clear all rational real and imaginary denominators of both recipes at once. The positive square of that nonzero denominator cancels in the budget. Rat.denseRange_cast, DenseRange.piMap and closedness of the finite polynomial inequality extend the budget to all complex coefficients on that finite subset. This continuity is a theorem about coefficient space, with no topology on X and no physical-control assumption.

The structural step uses the extended budget on t f and (t+i) f. Its difference is Re Q(f)+2t Im Q(f), for every real t. A nonzero imaginary part would allow an explicitly chosen t with negative difference. Thus self-comparisons are real; Mathlib's LinearMap.isSymmetric_iff_inner_map_self_real and Matrix.isSymmetric_toEuclideanLin_iff recover the original matrix's Hermitian symmetry. The zero-recipe test gives its nonnegative quadratic form. Conversely, Hermitian positive type makes the budget difference the nonnegative quadratic form of f-g. Restriction supplies both smaller coefficient domains.

The raw readout is compared with finite subset tables through Finsupp.sum_of_support_subset, Finsupp.sum_embDomain and Finsupp.sum_fintype. The finite-subset argument retains the original entries of K throughout. Zero kernels, empty supports and null vectors require no division by a quadratic value or invertible Gram matrix. Formal recipe operations and coefficient approximation supply no physical copying, amplification, coherent preparation, measurement interface or physical continuity.

## References

- Truth anchor: `D5/S3/Quantum/Completion/IntegerMutualReadout.Budget`
- Truth anchor: `D5/S3/Quantum/Completion/IntegerMutualReadout.mutual_budget_iff_positive_type`
- Truth anchor: `D5/S3/Quantum/Completion/IntegerMutualReadout.rationalComplex`
- Truth anchor: `D5/S3/Quantum/Completion/IntegerMutualReadout.readout`
