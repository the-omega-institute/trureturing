# Actual Positive Shear Fibers

## Abstract

Entire positive shear fibers determine globally attaining causal policies and exact literal action minima.

Every globally valid original three-read protocol is proved to select a positive U or V shear after each positive initial read; this is a consequence of arbitrary-history correctness, not an additional policy assumption. Every positive source has a positive factorization R=c l with one row l fixed throughout the run, and every literal word reads l(E(w)c)=trace(E(w)R).

Fix positive reals x,z and a positive natural k. True denotes U^k with rows (1,k),(0,1), and false denotes V^k with rows (1,0),(k,1). The upper fiber has rows (x-s,s(x-s)/z),(z,s); the lower fiber has rows (x-s,z),(s(x-s)/z,s), with exactly 0<s<x. Both reads are x and x+kz. Every compatible positive rank-one source has this form.

For B=E(w)U^k set e=B21; for B=E(w)V^k set e=B12. In both cases D=B22-B11 and the third read is t0+Ds+(e/z)s(x-s). t0=B11 x+B12 z in the upper branch, and B11 x+B21 z in the lower.

**Theorem 1.1 (Full-fiber injectivity, literal lengths, and native selected queries).**

$$\forall upper,x,z,k,w, \operatorname{PositiveParameters}\left(x, z, k\right) \implies \operatorname{DerivedSecondShear}\left(x\right) \land \operatorname{FixedGaugeFactorization}\left(\right) \land \operatorname{ExactFiber}\left(upper\right) \land (\operatorname{Injective}\left(B\right) \Leftrightarrow e >0 \land e\frac{x}{z} \leq\lvert D\rvert) \land \operatorname{LiteralMinimum}\left(upper\right) \land \operatorname{NativeThirdQuery}\left(upper\right) \land \operatorname{ExactRecoveryRange}\left(upper\right) \land \operatorname{CausalAttainingPolicy}\left(upper\right) \land \operatorname{ShortestPrefixAndOptimizedCost}\left(upper\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/SelfCalibratingFibers.full_fiber_and_signed_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All quantifiers include the entire open source fiber. If e=0 the raw signed relation forces D=0 and the read is constant. For e>0, injectivity is equivalent to |D|>=e x/z. Equality is allowed because the fiber endpoints are excluded. Failure places a quadratic vertex inside the interval and supplies two interior points with equal third reads.

Put rho=x/z, m=ceil(rho), and h=(length(w)+1)/2 with natural integer division. Every injective upper continuation has rho<=k+h; every injective lower continuation has rho<=k+h-1. The exact minimum literal lengths are 2 max(0,m-k-1)+1 and 2 max(0,m-k)+1. Alternating words starting with M or J attain the respective minima after the same fixed shear endpoint.

For an OriginalValid native policy selecting a literal second word with that endpoint, the common second history cannot stop. Its third query extends that exact paid word and is injective on every compatible source. Equal third reads would otherwise force the same terminal relation on two different sources. This uses arbitrary history selectors and the same retained source at every read; it assumes no finite candidate normalization. Every successful native run on every compatible source pays at least its original literal prefix length plus the branch minimum; the cost includes its unread terminal tail.

For every real a>=rho, put f(p)=z+ap+p(x-p)/z and K=x+az>=2x. Its exact image on 0<p<x is z<tau<z+ax. For an actual tau=f(p), the discriminant is (K-2p)^2>0, its positive square root is K-2p, and the other root K-p is strictly beyond x. The stable inverse is p=2z(tau-z)/(K+sqrt(K^2-4z(tau-z))). Upper recovery uses s=p and lower recovery uses s=x-p. The equality K=2x is included.

Let m=ceil(x/z). The upper policy selects N=max(k,m-1), executes N-k chronological M,J pairs then M, and has actual cumulative endpoint MU^N. The lower policy selects N=max(k,m), executes N-k J,M pairs then J, and has cumulative endpoint JV^N. The increasing coordinate is s above and p=x-s below, with a=N+1 or a=N. The selected words therefore have exactly the stated open ranges and recovery formulas, including the equality boundary.

Any functions of the initial read may choose direction, positive exponent, and a literal prefix representing that shear. The history-only optimalPolicy preserves this entire prefix. It obtains z=(y-x)/k from the second read, selects the shortest continuation, decodes its actual third read, and stops with no unread tail. On every positive rank-one source native execution has exactly three reads, follows chronological queries, returns the initial relation, and costs the paid prefix plus the exact branch minimum. No correctness premise is imposed on this policy.

The shortest prefix for U^k or V^k costs exactly 2k. Adding the continuation minima gives C_U=max(2k+1,2m-1) and C_V=max(2k+1,2m+1). These optimized values apply when the prefix is replaced before execution; an already executed redundant prefix always retains its literal paid cost.

These statements concern exact real reads and literal M/J action counts. They do not bound bit complexity or numerical precision, and no noisy inverse guarantee is asserted.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/SelfCalibratingFibers.full_fiber_and_signed_capacity`
- Dependency: [D5/S3/ConceptDynamics/Experiment/SelfCalibratingRulings](SelfCalibratingRulings.md)
