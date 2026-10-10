# The Unique Positive Rational Price

## Abstract

The unrestricted real-law optimum is positive rational and is the unique real zero of the triangular root value.

RealVector(m) is the space of real functions on Fin m. For natural m, L(p) is the sum over natural d of (2^d-sum_i floor(2^d p(i)))/2^d. The quantity alpha(m) is the infimum of L(p)/p(k) over all strictly positive normalized real vectors p on Fin m and every index k of a least coordinate. W(x,m,1) is the infimum of C-x*t over all legal triangular paths starting at residual one with m retained labels. Here C is the sum of the path residuals divided by 2^d and t is the anchor-digit mass. realCast denotes the canonical inclusion of rational numbers into the reals.

NonnegativeRationalLaw(m,p) means p has real coordinates indexed by Fin m, every coordinate is nonnegative, their sum is one, and for every i there exists a rational q whose real cast equals p(i).

Optimizer(m,p,k) means that p is strictly positive, its coordinates sum to one, p(k)<=p(i) for every i, and L(p)/p(k)=alpha(m). A triangular state (r,e) has 0<e, r<e, and e<=m. A one action requires e<=2r and has successor (2r-e,e). A zero action with h departures requires 2r<e and h<=2r, and has successor (2r-h,e-h). RootPath(m) starts at (1,m) and satisfies these bounds and successor conditions at every natural depth.

**Definition 1.1 (Joint probability, anchor and cost preservation).**

$$\forall m \in \mathbb{N}, \forall p \in \operatorname{RealVector}\left(m\right), \forall k \in \operatorname{Fin}\left(m\right), \operatorname{HasOptimalEmbedding}\left(m,p,k\right) \iff \exists sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(m\right)\right), \exists gamma \in \operatorname{RootPath}\left(m\right), (\forall i \in \operatorname{Fin}\left(m\right), \operatorname{probability}\left(gamma,i\right) = \operatorname{p}\left(\operatorname{sigma}\left(i\right)\right)) \land \operatorname{anchorMass}\left(gamma\right) = \operatorname{p}\left(k\right) \land \operatorname{pathCost}\left(gamma\right) = \operatorname{L}\left(p\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.HasOptimalEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The permutation is fixed for all depths. The path's label digits define probability by the sum of digit(i,d)/2^(d+1). Its anchor mass uses the permanent anchor digit in the same series. Its path cost is the sum of r(d)/2^d. All three equalities refer to this single path.

**Theorem 1.2 (Every attaining real law has this embedding).**

$$\forall m \in \mathbb{N}, (2 \le m) \to \forall p \in \operatorname{RealVector}\left(m\right), \forall k \in \operatorname{Fin}\left(m\right), \operatorname{Optimizer}\left(m,p,k\right) \to \operatorname{HasOptimalEmbedding}\left(m,p,k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.embedding_result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict rounding identifies the departure depth of each larger coordinate. Minimum coordinates are retained forever; every other coordinate remains until its least terminating depth. The floor residual is the sum of the retained fractional tails. A common anchor one digit forces e<=2r. A zero anchor digit forces 2r<e, because the anchor itself supplies one strict half-tail inequality. The retained-label count and residual recurrence jointly give every legal successor.

Sort the departure depths in descending order once, treating permanent labels as having infinite departure time. Permanent labels come first, and every retained set becomes an initial interval. The resulting legal path has precisely the original floor digits in that fixed order. Equality of all dyadic floor prefixes recovers the real probabilities. The minimum and cost identities then follow from the same path and the triangular normalization theorem. No rationality or computability restriction is placed on the input law.

**Theorem 1.3 (Rational coordinates give rational dyadic cost).**

$$\forall m \in \mathbb{N}, \forall p \in \operatorname{RealVector}\left(m\right), \operatorname{NonnegativeRationalLaw}\left(m,p\right) \to \exists v \in \mathbb{Q}, \operatorname{realCast}\left(v\right) = \operatorname{L}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.rational_law_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

For one rational coordinate, denominator residues take only finitely many values. A collision gives equal complete residue tails. Two prefix-plus-discounted-tail identities solve the common discounted series as a rational number. Summing these coordinate costs and using normalization gives the rational law cost. The denominator-residue method is classical; the displayed finite-law statement combines it with the floor cost expression.

**Theorem 1.4 (A positive rational representative of the full-real optimum).**

$$\forall m \in \mathbb{N}, (2 \le m) \to \exists A \in \mathbb{Q}, 0 < A \land \operatorname{realCast}\left(A\right) = \operatorname{alpha}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.rational_alpha` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an attaining law in the full real domain. Strict rounding makes every coordinate above its minimum dyadic. Normalization expresses the common minimum as one minus the sum of the larger rational coordinates, divided by the number of minimum coordinates. Thus this same attaining law has rational cost and rational positive minimum. Their quotient equals alpha(m), which is positive by the label-count lower bound.

**Theorem 1.5 (The zero over every real price).**

$$\forall m \in \mathbb{N}, (2 \le m) \to \forall x \in \mathbb{R}, (\operatorname{W}\left(x,m,1\right) = 0 \iff x = \operatorname{alpha}\left(m\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.zero_iff_alpha` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every triangular path satisfies C>=alpha(m)*t, and its root cost is at least one. The reverse embedding of an attaining law supplies a positive-anchor path with equality. Hence W vanishes at alpha. If a smaller price had value zero, a path attaining that value would contradict either the positive-anchor lower bound or the root cost bound. At a larger price the embedded optimizer has strictly negative value. These arguments quantify over every real x.

**Theorem 1.6 (Positive rational price and exact unrestricted equality).**

$$\forall m \in \mathbb{N}, (2 \le m) \to \exists A \in \mathbb{Q}, 0 < A \land \operatorname{realCast}\left(A\right) = \operatorname{alpha}\left(m\right) \land (\forall x \in \mathbb{R}, (\operatorname{W}\left(x,m,1\right) = 0 \iff x = \operatorname{realCast}\left(A\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same rational A is positive, has real value alpha(m), and is the unique zero of W(x,m,1). Rationality is derived from an attaining law, while uniqueness uses its cost-preserving triangular embedding. This does not assert a finite rational affine family for the entire price function, a finite maximal stopping depth, or any computational restriction on the optimization domain.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.HasOptimalEmbedding`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.embedding_result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.rational_alpha`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.rational_law_cost`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.zero_iff_alpha`
- Dependency: [D5/S1/Digit/RadixFloorDigit](../../../../S1/Digit/RadixFloorDigit.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding](StrictRounding.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope](../OptimalLawStrictSlope.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence](../TriangularFirstSplitRecurrence.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization](../TriangularPathNormalization.md)
