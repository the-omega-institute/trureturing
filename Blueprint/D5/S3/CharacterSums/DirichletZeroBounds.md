# Ordinary zeros with their full multiplicities

## Abstract

An inverse-square budget for every Dirichlet zero

**Definition 1.1 (The corrected completed-zero budget).**

$$\forall q \in \operatorname{Naturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \forall t \in \operatorname{Reals}\left(\right),\; \operatorname{completionBudget}\left(chi, t\right) = \operatorname{add}\left(\operatorname{div}\left(\operatorname{sub}\left(\operatorname{add}\left(\operatorname{sub}\left(\operatorname{add}\left(\operatorname{sub}\left(\operatorname{log}\left(q\right), \operatorname{log}\left(\operatorname{pi}\left(\right)\right)\right), \operatorname{log}\left(\operatorname{add}\left(\operatorname{abs}\left(t\right), 3\right)\right)\right), \operatorname{log}\left(2\right)\right), \operatorname{div}\left(1, 2\right)\right), \operatorname{re}\left(\operatorname{inverse}\left(\operatorname{add}\left(2, \operatorname{add}\left(\operatorname{parity}\left(chi\right), \operatorname{mul}\left(\operatorname{realToComplex}\left(t\right), \operatorname{imaginaryUnit}\left(\right)\right)\right)\right)\right)\right)\right), 2\right), \operatorname{add}\left(\operatorname{div}\left(\operatorname{log}\left(2\right), 4\right), \operatorname{add}\left(\operatorname{div}\left(\operatorname{mul}\left(4, \operatorname{log}\left(3\right)\right), 9\right), \operatorname{div}\left(1, 3\right)\right)\right)\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletZeroBounds.completionBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let a be zero for an even character and one otherwise. Uχ(t) = (log(q)-log(π)+log(|t|+3)-log(2)+1/2 - Re(1/(2+a+it)))/2 + K₀, with K₀ = log(2)/4+4log(3)/9+1/3 < 1. The real Gamma correction and the explicit arithmetic constant remain visible. The logarithmic series bound separates the terms at two and three. Mathlib's log_div_self_rpow_antitoneOn and sum_le_integral compare each finite tail with an integral. WeightedStieltjes's public intervalIntegral_log_add_two_div_sq_eq evaluates it, and its nonnegative endpoint remainder gives (1+log(3))/3.

**Theorem 1.2 (The full zero budget).**

$$\forall q \in \operatorname{PositiveNaturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \operatorname{implies}\left(\operatorname{primitiveNonprincipal}\left(chi\right), \forall T \in \operatorname{Reals}\left(\right),\; \forall t \in \operatorname{Reals}\left(\right),\; \operatorname{implies}\left(\operatorname{le}\left(\operatorname{abs}\left(t\right), T\right), \operatorname{and}\left(\operatorname{ZeroRealPartsStrictlyBelowOne}\left(chi\right), \operatorname{and}\left(\operatorname{SummableInverseSquares}\left(\operatorname{LFunction}\left(chi\right), t\right), \operatorname{and}\left(\operatorname{lt}\left(\operatorname{weightedInverseSquareSum}\left(\operatorname{LFunction}\left(chi\right), t\right), \operatorname{add}\left(\operatorname{div}\left(\operatorname{log}\left(\operatorname{mul}\left(q, \operatorname{add}\left(\operatorname{abs}\left(t\right), 3\right)\right)\right), 2\right), \operatorname{div}\left(7, 4\right)\right)\right), \operatorname{and}\left(\operatorname{le}\left(\operatorname{weightedInverseSquareSum}\left(\operatorname{LFunction}\left(chi\right), t\right), \operatorname{add}\left(\operatorname{log}\left(\operatorname{mul}\left(q, \operatorname{add}\left(T, 3\right)\right)\right), 4\right)\right), \operatorname{le}\left(\operatorname{weightedInverseSquareSum}\left(\operatorname{LFunction}\left(chi\right), t\right), \operatorname{add}\left(\operatorname{completionBudget}\left(chi, t\right), \operatorname{half}\left(\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletZeroBounds.zero_square_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let χ be a primitive nonprincipal complex Dirichlet character modulo a positive q. For any real T and t with |t| ≤ T, all ordinary L-function zeros have real part strictly below one. Their inverse-square sum at 2+it, with analytic multiplicity, is summable and at most log(q(T+3))+4. The height condition already forces T ≥ 0; no separate assumption is needed.

The ordinary zero divisor is the disjoint union of the completed zero divisor in the open critical strip and the simple parity lattice -a-2n, where a is zero for an even character and one otherwise. The explicit bijection preserves the completed multiplicities and assigns multiplicity one to each parity zero, including zero for even characters.

The completed contribution is at most Uχ(t) and strictly below log(q(|t|+3))/2 + 5/4. For the lattice, the real distance is at least 2(n+1). The integral test gives Σ (n+1)^(-2) ≤ 2, so its contribution is at most 1/2. The full sum is therefore at most Uχ(t)+1/2 and strictly below log(q(|t|+3))/2 + 7/4. Logarithmic monotonicity and q ≥ 1 give the common height budget log(q(T+3))+4. All three bounds are included in the public conclusion.

This theorem concerns all zeros of the actual Dirichlet L-function, including every trivial zero. It is a uniform analytic budget and supplies no one-sided arithmetic moment inequalities.

## References

- Truth anchor: `D5/S3/CharacterSums/DirichletZeroBounds.completionBudget`
- Truth anchor: `D5/S3/CharacterSums/DirichletZeroBounds.zero_square_bound`
- Dependency: [D5/S3/CharacterSums/DirichletTrivialZeros](DirichletTrivialZeros.md)
- Dependency: [D5/S3/Weil/Mertens/Cryptids/DigammaBinet/Foundation](../Weil/Mertens/Cryptids/DigammaBinet/Foundation.md)
- Dependency: [D5/S3/Weil/Mertens/Cryptids/WeightedStieltjes](../Weil/Mertens/Cryptids/WeightedStieltjes.md)
