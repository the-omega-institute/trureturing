# Finite Fibers Preserve Topological Entropy

## Abstract

A compact factor map with a uniform bound on its finite fibers preserves topological entropy.

Let X and Y be compact uniform spaces, with Y Hausdorff. Let S:X→X be continuous, and let π:X→Y be a continuous surjection satisfying π∘S=T∘π. Every fiber π⁻¹{y} is finite and its cardinality is at most the same natural number M. The covering entropy of S equals that of T. This formalizes the classical finite-to-one factor theorem; no literature novelty is claimed.

**Theorem 1.1 (Entropy equality under uniformly finite fibers).**

$$\begin{aligned}\forall X: Type, \forall Y: Type,\\{[\operatorname{UniformSpace}(X)] [\operatorname{CompactSpace}(X)] [\operatorname{UniformSpace}(Y)] [\operatorname{CompactSpace}(Y)] [\operatorname{T2Space}(Y)],}\\\forall S: X \to X, \forall T: Y \to Y, \forall \pi: X \to Y,\\\operatorname{Continuous}(S) \Rightarrow \operatorname{Continuous}(\pi) \Rightarrow\\\operatorname{Function.Surjective}(\pi) \Rightarrow \operatorname{Function.Semiconj}(\pi, S, T) \Rightarrow\\\forall M: \mathbb{N},\\{\forall y: Y, \operatorname{Set.Finite}(\operatorname{Set.preimage}(\pi, \operatorname{Set.singleton}(y))) \land \operatorname{Set.ncard}(\operatorname{Set.preimage}(\pi, \operatorname{Set.singleton}(y))) \le M} \Rightarrow\\\operatorname{Dynamics.coverEntropy}(S, \operatorname{Set.univ}()) = \operatorname{Dynamics.coverEntropy}(T, \operatorname{Set.univ}())\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/FiniteFiberEntropy.finite_fiber_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rufus Bowen (1971). *Entropy for group endomorphisms and homogeneous spaces*. DOI: [10.1090/S0002-9947-1971-0274707-X](https://doi.org/10.1090/S0002-9947-1971-0274707-X). URL: <https://doi.org/10.1090/S0002-9947-1971-0274707-X>.

*Commentary.*

For a symmetric source entourage U and fixed block length n, the n-step balls centered on a fiber cover that fiber using at most M centers. Since π is a closed map, this cover extends to the inverse image of a neighborhood of the base point. The Lebesgue number lemma makes the base entourage uniform over Y.

Over r consecutive blocks, each base covering orbit has at most M^r center codes. One actual orbit representative from every nonempty code class gives a source cover at entourage U∘U. No continuous selection of fiber points or lifting of a prescribed orbit is assumed. The source covering number at time n*r is at most M^r times the base covering number. Monotonicity permits restriction to these multiples; their extra entropy is log(M)/n, which tends to zero.

The reverse inequality reuses Mathlib's coverEntropy_image_le_of_uniformContinuous. The proof handles empty spaces, M=0 when both spaces are empty, and infinite entropy. It does not require T to be continuous or X to be Hausdorff. Finiteness of fibers is an explicit hypothesis: Set.ncard alone cannot express a finite bound because it is zero on an infinite set. The result supplies the entropy comparison needed by finite symbolic codings of compact dynamical systems; constructing a coding and proving its uniform fiber bound remain application-specific obligations.

## References

- Truth anchor: `D5/S1/Dynamics/FiniteFiberEntropy.finite_fiber_entropy`
