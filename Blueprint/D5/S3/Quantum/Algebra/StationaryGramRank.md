# Stationary Gram Rank

## Abstract

A finite occupation recurrence bounds the nullity of a normalized positive semidefinite matrix.

**Theorem 1.1 (The finite-box rank bound).**

$$\forall sigma: Type, \operatorname{Fintype}\left(sigma\right),\ \forall a: sigma \to Nat,\ \forall B: \operatorname{Matrix}\left(\operatorname{TailBox}\left(a\right), \operatorname{TailBox}\left(a\right), Complex\right),\ \operatorname{PosSemidef}\left(B\right) \implies\ \operatorname{B}\left(0, 0\right) = 1 \implies\ (\forall r, s: \operatorname{TailBox}\left(a\right), r \neq 0 \implies s \neq 0 \implies\ \operatorname{B}\left(r, s\right) = \sum_{i \in sigma} \operatorname{if}\left(0 < \operatorname{val}\left(\operatorname{r}\left(i\right)\right) \land 0 < \operatorname{val}\left(\operatorname{s}\left(i\right)\right), \operatorname{B}\left(\lambda j: sigma, \operatorname{FinMk}\left(\operatorname{NatSub}\left(\operatorname{val}\left(r(j)\right), \operatorname{if}\left(j = i, 1, 0\right)\right)\right), \lambda j: sigma, \operatorname{FinMk}\left(\operatorname{NatSub}\left(\operatorname{val}\left(s(j)\right), \operatorname{if}\left(j = i, 1, 0\right)\right)\right)\right), 0\right)) \implies\ \operatorname{NatSub}\left(\prod_{i \in sigma} (\operatorname{a}\left(i\right) + 1), \operatorname{FinsetSup}\left(\operatorname{univ}\left(sigma\right), a\right)\right) \leq \operatorname{rank}\left(B\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StationaryGramRank.stationary_gram_rank_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let sigma be any finite type and let a map sigma to the natural numbers. The set TailBox(a) consists of functions r with r(i) in Fin(a(i)+1). Its zero element has every coordinate zero. Let B be a complex matrix indexed by this box. Assume B is positive semidefinite and B(0,0)=1. For each pair of nonzero box elements r and s, assume B(r,s) is the sum over i of B(r-e(i),s-e(i)), including a summand only when both r(i) and s(i) are positive. Each coordinate of r-e(i) is the natural truncated difference r(j) minus one if j=i, and r(j) otherwise. These lowerings remain in the same box.

Then rank B is at least the product of a(i)+1 minus the finite supremum of a(i). The subtraction in this bound is natural subtraction. The supremum is zero and the product is one for an empty sigma. No positivity of the capacities or of individual matrix entries is required. In particular, the assertion includes all-zero capacities and supremum zero or one. The recurrence is required only when both indices are nonzero.

Define T(i) on coordinate basis vectors by lowering the i-th coordinate when that coordinate is positive, and sending the vector to zero otherwise. If u(0)=0, the recurrence gives u*Bu equal to the sum of (T(i)u)*B(T(i)u). Terms with a zero row or column vanish because u(0)=0. When u belongs to the kernel of B, this sum is zero. Positive semidefiniteness makes every summand nonnegative, so each is zero and every T(i)u also belongs to the kernel.

Send the coordinate basis vector at r to the monomial x^r divided by the product of the factorials r(i)!. This is a linear isomorphism onto the polynomials supported on exponents bounded by a. The nonzero factorial factors rescale the monomial basis. The identity n!=n(n-1)! shows that this map J satisfies partial(i)(J(u))=J(T(i)u), and its constant coefficient is u(0).

Let L be the image under J of the kernel of B. If a constant c belongs to L, injectivity of J identifies its inverse image with c times the coordinate vector at zero. The zero row of the kernel equation and B(0,0)=1 then give c=0. The conditional lowering property gives closure of L under partial derivatives of members with zero constant coefficient. Its support is rectangular, so the rectangular polynomial nullity bound gives dim L at most the finite supremum of a. Injectivity of J preserves the kernel dimension. Finally, the function space on TailBox(a) has dimension equal to the product of a(i)+1, and rank-nullity gives the claimed bound.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StationaryGramRank.stationary_gram_rank_lower_bound`
- Dependency: [D5/S1/Ledger/BoundedTimeSlice](../../../S1/Ledger/BoundedTimeSlice.md)
- Dependency: [D5/S3/Quantum/Algebra/RectangularPolynomialNullity](RectangularPolynomialNullity.md)
