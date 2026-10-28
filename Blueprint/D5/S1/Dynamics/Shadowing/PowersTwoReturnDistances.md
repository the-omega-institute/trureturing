# Powers-of-Two Return-Distance Example

## Abstract

An explicit binary two-sided subshift with neighborhood two-shadowing and without original exact-length quasi-finite type.

The source is Jonathan Meddaugh and Elyssa Stephens, Shadowing with small diameter sets of bounded cardinality, arXiv:2509.04312v1, https://arxiv.org/html/2509.04312v1, Definitions 2.1 and 3.5 and Question 5.3. The positive return distances are 2^j for natural j. Equivalently the intervening zero-run lengths are 2^j-1, including zero. The example uses the genuine compatible countable-product metric supplied by Mathlib, rather than the degenerate printed infimum expression in the source.

Question 5.3 asks: Are there subshifts with neighborhood 2-shadowing which are not a subshift of quasi-finite type? Here X consists of all binary configurations on the integers whose consecutive ones have distance in D={2^j:j>=0}; finite supports, singleton supports and the configuration with no ones are included. The shift is sigma(x)(k)=x(k+1). The consecutive-pair condition is closed and invariant under every integer shift, so X is a nonempty compact two-sided subshift.

The neighborhood two-shadowing assertion has the following quantifiers. For every epsilon>0 there is delta>0 such that every natural-time delta-pseudo-orbit z has one fixed nonempty finite subset A of X with cardinality at most two and initial diameter less than epsilon. At every natural time i, the actual distance from z(i) to sigma^i(A) is less than epsilon. The member of A providing this approximation may depend on i; A itself does not. This includes the initial diameter requirement of Definition 2.1.

The repair argument works for any return-distance set containing 1 and arbitrarily large positive integers, as expressed by unbounded_return_neighborhood_two. Choose a signed observation window of radius r controlling epsilon, an allowed distance h>2r, and delta forcing pseudo-orbit overlap on radius 2h. Extend the past by the orbit of z(0) and read the signed diagonal. Retain its ones from coordinate -r onwards. Every consecutive gap of length at most 2h is legal. In each forbidden longer gap (p,q), insert all ones from p+h through q-h. Its new edge distances are h and its interior distances are 1. One tracer uses this repaired support, the other retains only the initial support in [-r,r]. Both agree initially on that window. Windows containing an original one are unchanged by repair; windows containing no original one are traced by the second tracer.

Definition 3.5 asks for a threshold M such that, for every n>=M and language words u,v, a language word w of length exactly n with uw and wv allowed can be replaced by a word z of the same length n with uzv allowed. For any proposed M take n=max(M,1), H=2^(n+2), u=10^H, w=0^n and v=1. These are nonempty language words and uw,wv occur in singleton-support configurations. Any proposed bridge z of length n would force the first one after the leading one to occur at a distance in (H,H+n+1]. That interval lies strictly between the consecutive powers H and 2H, a contradiction. Thus the obstruction preserves the exact bridge length and the source's positive-length convention.

**Theorem 1.1 (The explicit return-distance example).**

$$\begin{aligned}\operatorname{Nonempty}(\operatorname{ReturnPoint}(\operatorname{powersTwoDistances}())) \land\\\operatorname{CompactSpace}(\operatorname{ReturnPoint}(\operatorname{powersTwoDistances}())) \land\\\operatorname{Continuous}(\operatorname{returnShift}(\operatorname{powersTwoDistances}())) \land\\\operatorname{NeighborhoodTwoShadowing}(\operatorname{returnShift}(\operatorname{powersTwoDistances}())) \land\\\neg \operatorname{ReturnQuasiFiniteType}(\operatorname{powersTwoDistances}())\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances.powers_two_return_distance_example` (`✓ std3`). ∎

*Resolves.* `Problems/meddaugh-stephens-2025-neighborhood-two-shadowing` (proved) by `D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances.powers_two_return_distance_example`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"meddaugh-stephens-2025-neighborhood-two-shadowing","declaration_gid":"D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances.powers_two_return_distance_example","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

A singleton-support configuration witnesses nonemptiness. The phase space is the carrier of the bundled finite-alphabet subshift on integer coordinates. All pseudo-orbit time indices remain natural numbers. Distance one is allowed and powers of two are unbounded, so the generic gap-repair theorem supplies the original finite-set two-shadowing property. For every n choose H=2^(n+2)>n+1. The interval (H,H+n+1] lies strictly between H and 2H and contains no power of two. The generic first-return language obstruction therefore disproves the original exact-length QFT condition. This explicit example gives an affirmative answer to the existence request of Question 5.3 with the genuine compatible product metric.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances.powers_two_return_distance_example`
- Dependency: [D5/S1/Dynamics/Shadowing/ReturnDistanceShadowing](ReturnDistanceShadowing.md)
