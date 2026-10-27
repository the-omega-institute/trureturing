# Powers-of-Two Return-Distance Example

## Abstract

An explicit binary two-sided subshift with neighborhood two-shadowing and without original exact-length quasi-finite type.

The source is Jonathan Meddaugh and Elyssa Stephens, Shadowing with small diameter sets of bounded cardinality, arXiv:2509.04312v1, https://arxiv.org/html/2509.04312v1, Definitions 2.1 and 3.5 and Question 5.3. The positive return distances are 2^j for natural j. Equivalently the intervening zero-run lengths are 2^j-1, including zero. The example uses the genuine compatible countable-product metric supplied by Mathlib, rather than the degenerate printed infimum expression in the source.

**Theorem 1.1 (The explicit return-distance example).**

$$\begin{aligned}\operatorname{Nonempty}(\operatorname{ReturnPoint}(\operatorname{powersTwoDistances}())) \land\\\operatorname{CompactSpace}(\operatorname{ReturnPoint}(\operatorname{powersTwoDistances}())) \land\\\operatorname{Continuous}(\operatorname{returnShift}(\operatorname{powersTwoDistances}())) \land\\\operatorname{NeighborhoodTwoShadowing}(\operatorname{returnShift}(\operatorname{powersTwoDistances}())) \land\\\neg \operatorname{ReturnQuasiFiniteType}(\operatorname{powersTwoDistances}())\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances.powers_two_return_distance_example` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singleton-support configuration witnesses nonemptiness. The phase space is the carrier of the bundled finite-alphabet subshift on integer coordinates. All pseudo-orbit time indices remain natural numbers. Distance one is allowed and powers of two are unbounded, so the generic gap-repair theorem supplies the original finite-set two-shadowing property. For every n choose H=2^(n+2)>n+1. The interval (H,H+n+1] lies strictly between H and 2H and contains no power of two. The generic first-return language obstruction therefore disproves the original exact-length QFT condition. This theorem addresses this explicit example and the existence request of Question 5.3 only. It asserts no full hierarchy result, nonsoficity theorem, literature novelty or official acceptance.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances.powers_two_return_distance_example`
- Dependency: [D5/S1/Dynamics/Shadowing/ReturnDistanceShadowing](ReturnDistanceShadowing.md)
