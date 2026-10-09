# Actual Native Marginal Indicators and Strict Local Gram

## Abstract

Every original position has a positive five-mode marginal and three noncentered normalized indicators in that marginal's one L2 space.

The source and laws are the original JointLaw.Source(n) and law(n,t,e). The initial seam is false, each printed triple is read from high bit to low bit, and the window list keeps its chronological order. The terminal seam is unrestricted. Null prefixes and the all-null source belong to this same domain. Position i in Fin n corresponds to the original position j=i.val+1.

**Definition 1.1 (A source realizing each local mode).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.isolated`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.isolated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

isolated(i,a) places a at position i and the null mode everywhere else. It is legal for every finite length, position and one of the five modes. A null suffix is legal at either incoming seam, including the true seam left by a low or endpoint mode.

**Definition 1.2 (Mass from the original full source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.modeMass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.modeMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

modeMass(n,t,e,i,a) is mass(law(n,t,e),w(i)=a), summed over the entire original Source(n). It is not a product-law or Markov approximation.

**Definition 1.3 (The actual marginal probability measure).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.marginalMeasure`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.marginalMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n at least three, 0<t<1 and e equal to minus one or one, marginalMeasure(n,t,e,i) is the discrete probability measure whose singleton masses are modeMass(n,t,e,i,a). The theorem identifies its mass on every set with the corresponding original-source event mass.

**Definition 1.4 (Probability and finite event measures).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.marginal_finite`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.marginal_finite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual marginal has total mass one. Every occupancy event therefore has finite measure and defines a constant indicator in L2.

**Definition 1.5 (The three original occupancy events).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.occupancy`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.occupancy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

occupancy(0) is the set containing low and ends, occupancy(1) contains high and ends, and occupancy(2) contains middle. These are x,y,z respectively. The endpoint event is their first two sets' intersection, while the third is disjoint from both.

**Definition 1.6 (Noncentered vectors in one actual L2).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.normalizedIndicator`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.normalizedIndicator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalizedIndicator(n,t,e,i,r) is the constant-one indicator of occupancy(r), multiplied by the reciprocal square root of its actual marginal event mass. All three vectors belong to Lp(R,2,marginalMeasure(n,t,e,i)); no mean is subtracted.

**Definition 1.7 (The three-index actual Gram).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.localGram`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.localGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

localGram(n,t,e,i)(r,s) is the real L2 inner product of normalizedIndicator(n,t,e,i,r) and normalizedIndicator(n,t,e,i,s). Its two indices both range over Fin 3.

**Definition 1.8 (The actual X,Y,Z means).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.means`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.means` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

means(n,t,e,i,0)=modeMass(low)+modeMass(ends), means(n,t,e,i,1)=modeMass(high)+modeMass(ends), and means(n,t,e,i,2)=modeMass(middle), with the same n,t,e,i in every term.

**Definition 1.9 (The normalized same-window endpoint mass).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.coupling`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.coupling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

coupling(n,t,e,i)=modeMass(n,t,e,i,ends)/sqrt(means(n,t,e,i,0)*means(n,t,e,i,1)). The numerator is the original kappa. Strict positivity of the low, high and endpoint modes makes this ratio strictly between zero and one.

**Theorem 1.10 (Positive actual marginal and exact normalized Gram).**

$$\forall n: \mathbb{N}, ((3 \le n) \implies (\forall t: \mathbb{R}, (((0 < t) \land (t < 1)) \implies (\forall e: \mathbb{Z}, ((e = -1 \lor e = 1) \implies (\forall i: \operatorname{Fin}\left(n\right), ((\forall E: \operatorname{Set}\left(Window\right), (\operatorname{real}\left(\operatorname{mu}\left(n, t, e, i\right), E\right) = \operatorname{mass}\left(\operatorname{law}\left(n, t, e\right), \operatorname{event}\left(i, E\right)\right))) \land (\forall a: Window, (0 < \operatorname{modeMass}\left(n, t, e, i, a\right))) \land (\forall r: \operatorname{Fin}\left(3\right), (0 < \operatorname{means}\left(n, t, e, i, r\right))) \land ((0 < \operatorname{coupling}\left(n, t, e, i\right)) \land (\operatorname{coupling}\left(n, t, e, i\right) < 1)) \land (\operatorname{localGram}\left(n, t, e, i\right) = \operatorname{U}\left(\operatorname{coupling}\left(n, t, e, i\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.native_local_indicator_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula, mu(n,t,e,i) abbreviates marginalMeasure, event(i,E) is the predicate w(i) in E on Source(n), and U(c) is the three-by-three matrix with rows (1,c,0), (c,1,0), (0,0,1). Every auxiliary expression retains the same original position and source law.

A legal source with only the chosen local mode makes every singleton event nonempty. Strict positivity of the full source law gives positive mass to all five modes. Summing these masses gives the actual marginal probability measure. The L2 indicator inner product is the measure of the intersection, so the three normalized vectors have the displayed Gram. The positive low and high masses give X*Y greater than kappa squared.

The statement ranges over every original position and both signs separately. Equality between the two signs, the eigenvalue multiset, the original piecewise Psi functional, independence from t, and the all-position Fibonacci quotient are additional assertions.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.coupling`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.isolated`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.localGram`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.marginalMeasure`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.marginal_finite`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.means`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.modeMass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.native_local_indicator_gram`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.normalizedIndicator`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/LocalIndicators.occupancy`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw](JointLaw.md)
