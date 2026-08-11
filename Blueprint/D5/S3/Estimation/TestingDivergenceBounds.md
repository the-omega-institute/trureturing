# Divergence Bounds for Finite Two-Point Testing Error

## Abstract

Divergence bounds make Le Cam's exact finite testing-error floor operational and expose the complementary regimes of Pinsker and Bretagnolle--Huber.

**Theorem 1.1 (Bretagnolle--Huber remains informative after Pinsker degenerates).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\\forall A: \operatorname{Finset}(\iota),\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land\\((\forall i, 0\le q(i)) \land \sum _{i} q(i)=1) \land\\(\forall i, q(i)=0 \Rightarrow p(i)=0)) \Rightarrow \\1-\sqrt {1-\exp (-D_{\operatorname{KL}}(p \Vert q))}\le \sum _{i\in A} p(i)+\sum _{i\in A^c} q(i).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TestingDivergenceBounds.testing_error_bretagnolle_huber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Waves 40 and 41 fixed the minimum over all finite two-point tests at exactly one minus total variation. That exact characterization is structural but is not generally a model-level quantity one can calculate directly. A divergence often is calculable, or admits a tractable model-specific upper bound. The present module therefore re-expresses the frozen testing floor in terms of relative entropy.

The two bounds are chained corollaries, not new mathematics. Each is Le Cam's frozen bound composed with a frozen total-variation-versus-divergence inequality. The module consumes Pinsker and Bretagnolle--Huber; it does not re-derive either. The declaration testing_error_pinsker gives total error at least 1-sqrt(D/2), while testing_error_bretagnolle_huber gives total error at least 1-sqrt(1-exp(-D)). A downstream estimation argument can therefore use divergence directly.

Their assumptions are exactly the union required by the frozen inputs. Le Cam requires equal total mass and unit mass. Pinsker and Bretagnolle--Huber additionally require pointwise nonnegativity of both laws and the discrete absolute-continuity convention q(i)=0 implies p(i)=0. Apart from the finite carrier and the supplied test event, the composed statements add no hypothesis of their own. The composition is therefore tight at the level of assumptions rather than lossy.

The comparison is the module's central result. The theorem pinsker_floor_nonpos_of_two_le proves, for every real D at least two, that the Pinsker-form floor 1-sqrt(D/2) is nonpositive. It is exactly zero at D=2 and decreases thereafter; at D=10 it is approximately -1.24. Such a right side says nothing: total testing error is a sum of masses and is already bounded below by zero.

The theorem bretagnolle_huber_floor_pos proves the contrasting fact for every real D, without restricting D to be nonnegative: the floor 1-sqrt(1-exp(-D)) is strictly positive. At D=2 it is approximately 0.0701, and at D=10 it is approximately 2.27e-5. The latter value is small but remains strictly positive, so the Bretagnolle--Huber form never degenerates at any finite real argument.

This is the estimation-side payoff of proving Bretagnolle--Huber four waves after Pinsker. Pinsker is sharper when the laws are close; only Bretagnolle--Huber continues to say something when they are far apart. The two inequalities are complementary in precisely the sense claimed by the Bretagnolle--Huber wave, and the present module makes that claim operational for testing error rather than leaving it as a comparison of total-variation upper bounds.

The proof architecture contains no hidden analytic step. Each testing theorem first substitutes its frozen total-variation upper bound into one minus total variation and then applies Le Cam's frozen total-error bound to the supplied event. The two scalar comparison theorems isolate the operational difference: elementary square-root monotonicity makes the Pinsker floor nonpositive from two onward, while positivity of the exponential keeps the Bretagnolle--Huber square root strictly below one.

No minimax or sample-complexity corollary, multi-point generalization, measure-theoretic analogue, or theorem deciding which bound is sharper throughout the intermediate regime is claimed. Beyond the two proved floor facts, no crossover point is asserted. Relative entropy uses the natural logarithm, so all divergence values in these statements are in nats.

## References

- Truth anchor: `D5/S3/Estimation/TestingDivergenceBounds.testing_error_bretagnolle_huber`
- Dependency: [D5/S3/Estimation/LeCamTight](LeCamTight.md)
- Dependency: [D5/S3/TotalVariation/Bhattacharyya](../TotalVariation/Bhattacharyya.md)
