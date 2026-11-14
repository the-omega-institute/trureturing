# Interval assignments and their uniform conditional laws

## Abstract

Exact exterior-conditioned coupling on either side of a single disagreement.

Let W(n) be Fin n to Bool, and let A(k,n,w) mean DBonacciAdmissible. For a finite set B of sites, Assign(B) is the type of Boolean functions on the subtype of sites belonging to B. Restricting a full word w to that subtype gives restrictBlock(B,w). The law L(k,B,x,h) is conditionalBlockLaw: the pushforward to Assign(B) of the uniform law on legal full words agreeing with x at every site in the full complement of B. Here h certifies legality of x and hence nonemptiness. Two completions with the same restriction agree inside B and at all exterior sites, so restriction is injective on that fiber. Thus this pushforward is the uniform law on legal B assignments with that exterior.

H(B,p) denotes blockHamming, the sum over sites i in B of the indicator that the two assignments p.first(i) and p.second(i) differ. E(J,H(B)) denotes the ENNReal sum over assignment pairs p of J(p)H(B,p). All sites of the exterior are retained, including both ends of the interval.

**Theorem 1.1 (An actual joint law with exact block marginals and cost at most one).**

$$(\forall (k,n:\mathbb{N}), (((2 \leq k) \implies ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((\forall (h:\operatorname{A}\left(k, n, x\right)), ((\forall (g:\operatorname{A}\left(k, n, y\right)), ((\forall (a,b,u:\operatorname{Fin}\left(n\right)), (((((a \leq b) \land (\neg (u \in \operatorname{Icc}\left(a, b\right))) \land ((\forall (i:\operatorname{Fin}\left(n\right)), (((i \neq u) \implies (\operatorname{at}\left(x, i\right) = \operatorname{at}\left(y, i\right)))))))) \implies ((\exists (J:\operatorname{PMF}\left(\operatorname{Assign}\left(\operatorname{Icc}\left(a, b\right)\right) \times \operatorname{Assign}\left(\operatorname{Icc}\left(a, b\right)\right)\right)), ((\operatorname{mapFst}\left(J\right) = \operatorname{L}\left(k, \operatorname{Icc}\left(a, b\right), x, h\right)) \land (\operatorname{mapSnd}\left(J\right) = \operatorname{L}\left(k, \operatorname{Icc}\left(a, b\right), y, g\right)) \land (\operatorname{E}\left(J, \operatorname{H}\left(\operatorname{Icc}\left(a, b\right)\right)\right) \leq 1)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciIntervalBlockCoupling.conditional_interval_block_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put B=Icc(a,b). The assumption a at most b makes B nonempty; it may touch either endpoint of the word or have length smaller than k. Since u is outside this interval, either u is before every site of B or after every site of B. In the first case sort B increasingly and apply the conditional recursive scan. Its full-word projections are the exact completion laws and its expected internal Hamming cost is at most one. In the second case reverse all coordinates by Fin.rev. The existing forbidden-window reversal theorem proves legality is preserved. Reversal is an involutive bijection between the actual fixed-coordinate completion fibers, so it transports their uniform PMFs exactly. Apply the increasing scan to the reflected block, reverse both sampled full words back, and then restrict to B. The same site bijection preserves the Hamming sum. Composition of PMF maps proves both displayed marginal equalities. The proof uses the direct expected-cost estimate; it makes no claim about an explicit geometric survival-event tail.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciIntervalBlockCoupling.conditional_interval_block_coupling`
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling](KBonacciConditionalBlockCoupling.md)
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciIntegerInterval](KBonacciIntegerInterval.md)
