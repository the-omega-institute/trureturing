# Entropy of a Commonly Determined State

## Abstract

A finite state determined by either coordinate has entropy bounded by their mutual information.

**Theorem 1.1 (A commonly determined state is controlled by mutual information).**

$$\begin{gathered}\forall X, Y, C,\\[\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)] [\operatorname{Fintype}(C)],\\p: X\times Y\to \mathbb{R},\\a: X\to C, b: Y\to C,\\((\forall x, y, 0\leq p(x, y)) \land \sum_{x,y}p(x, y)=1),\\(\forall x, y, p(x, y)\neq0 \Rightarrow a(x)=b(y)) \Rightarrow\\H(a_{*}p_{X}) \leq I_{p}(X;Y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/CommonStateEntropyBound.common_state_entropy_le_mutual_information` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a normalized nonnegative mass function on finite X times Y. Let a : X -> C and b : Y -> C be deterministic maps into a finite common-state carrier. Assume a(x) = b(y) whenever the joint cell p(x,y) has nonzero mass. Then the entropy of the pushforward of the X-marginal through a is at most the mutual information of p.

The support-qualified agreement is exactly the almost-sure statement that one common random state is determined from either coordinate. Zero-mass cells impose no agreement requirement and do not change the induced common-state law.

The proof extends the joint law by the deterministic Y-to-C channel and applies the existing Markov data-processing inequality. Support agreement turns the X,C projection into the graph of a; the existing mutual-information entropy balance then identifies the information in that graph with the entropy of the common state. Loogle, LeanSearch, pinned-Mathlib, repository, and digestion-record searches found no exact theorem to bind.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/CommonStateEntropyBound.common_state_entropy_le_mutual_information`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Entropy/Submodularity/MarkovDataProcessing](MarkovDataProcessing.md)
