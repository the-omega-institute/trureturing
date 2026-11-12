# Least confirmation and positive dual frames

## Abstract

Least confirming effects generate every positive functional on a finite dimensional carrier.

Let A be a finite dimensional real vector space, P an arbitrary set of probes, and u a linear functional with u(p)=1 for every p in P. A functional is positive when its values on P are nonnegative. Every probe p has a linear functional e_p with 0<=e_p(q)<=1 for all q in P and e_p(p)=1. It is least among all such proper effects confirming p: if 0<=g(q)<=1 on P and g(p)=1, then e_p(q)<=g(q) on P. Finally, every nonzero positive functional has a strictly positive maximum attained at a probe. The set P need not be finite, and no separate spanning premise is used.

For a nonzero positive f, choose p with m=f(p)>0 maximal. The proper effect f/m confirms p, so leastness gives m e_p<=f. The residual r=f-m e_p is positive and vanishes at p. If f(q)=0, positivity of r and e_p also gives r(q)=0. Thus the span of zero probes can only grow. It grows strictly, because f vanishes on the old span but f(p)>0. Strong induction on the complementary dimension therefore terminates after at most dim(A) subtractions. Zero has the empty expansion, including when A has dimension zero.

Each later selected effect vanishes at every earlier selected probe. Moreover e_q(p)=0 implies e_p(q)=0: the proper effect u-e_q confirms p, so leastness gives e_p<=u-e_q, and evaluation at q gives the result. Thus the selected probes and their confirming effects are biorthogonal. To bound their sum, apply induction from the tail: u minus the sum of the tail effects is proper and confirms the head probe, so it dominates the head effect. Hence the total effect is at most u, and the unused effect is positive.

**Theorem 1.1 (Positive dual decomposition in a proper frame).**

Lean statement: `D5/S3/Quantum/Foundation/LeastConfirmationGeneration.positive_dual_generation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/LeastConfirmationGeneration.positive_dual_generation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive f has a list of at most dim(A) pairs (c_i,p_i), with c_i>0 and f=sum_i c_i e_(p_i). Distinct positions have both cross evaluations zero, while every diagonal evaluation is one. The unweighted effect sum is at most u. If f=u, evaluation at each selected probe forces c_i=1; the resulting effects sum exactly to u. On a nonzero normalized operational carrier this is a complete measurement. These conclusions do not require reciprocity, an inner product, spectrality, or reversible transformations.

The maximal-value subtraction method is adapted from Niestegge, arXiv:2312.13213v2, Lemma 3(iv), Lemma 5 and Theorem 2(i). The source's state-effect hypotheses are not identified with this interface; the proper-effect premise bridge and remaining differences are set out in Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge. No priority for the subtraction method or spectrality classification is claimed.

For the operational carrier of Definition 26.1, the intended probes are the extreme points of the compact normalized state base. A formal application must identify pointwise positivity and the full proper-effect interval with the cone order and derive positive maximum attainment at an extreme point. Those compact convex and normalization bridges are not proved here. The theorem takes maximum attainment as an explicit assumption.

This is a decomposition of positive linear functionals. A signed decomposition of every state-space vector still requires the state-effect correspondence and a faithful passage back to pure states, together with the compact-base bridges. Thus this result alone is not the implication from Principle S to Principle Sp for a general operational carrier. Reciprocity equates endpoint comparisons; it does not assert that successive physical measurements commute. No literature priority or empirical reconstruction is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/LeastConfirmationGeneration.positive_dual_generation`
