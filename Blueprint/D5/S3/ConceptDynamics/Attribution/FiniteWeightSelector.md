# Equivariant selection from finite weight profiles

## Abstract

Singleton weight fibers characterize admissible deterministic selection under label permutations.

**Theorem 1.1 (An equivariant selector exists exactly when each profile has an admissible singleton weight).**

$$\begin{gathered}\forall I,R:\operatorname{Type}, [\operatorname{Fintype}\left(I\right)] [\operatorname{LinearOrder}\left(R\right)],\\\forall D:\operatorname{Set}\left(I \to R\right), Allowed:\left(I \to R\right) \to \left(I \to Prop\right),\\(\forall g\in \operatorname{Perm}\left(I\right), \forall w\in D, \operatorname{permute}\left(g, w\right)\in D) \land (\forall g\in \operatorname{Perm}\left(I\right), \forall w:I \to R, \forall i\in I, \operatorname{Allowed}\left(\operatorname{permute}\left(g, w\right), \operatorname{g}\left(i\right)\right) \iff \operatorname{Allowed}\left(w, i\right)) \Rightarrow\\{}[(\exists s:D \to I, (\forall w\in D, \operatorname{Allowed}\left(w, \operatorname{s}\left(w\right)\right)) \land (\forall g\in \operatorname{Perm}\left(I\right), \forall w\in D, \operatorname{s}\left(\operatorname{permute}\left(g, w\right)\right)=\operatorname{g}\left(\operatorname{s}\left(w\right)\right))) \iff\\\forall w\in D, \exists i\in I, \operatorname{Allowed}\left(w, i\right) \land (\forall j\in I, \operatorname{w}\left(j\right)=\operatorname{w}\left(i\right)\Rightarrow j=i)]\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/FiniteWeightSelector.exists_equivariant_selector_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be a finite label type and R a linearly ordered weight type. A permutation g acts by composing a profile with the inverse of g. The set D of profiles is closed under this action, and each permutation carries admissible labels to admissible labels and conversely. Every profile in D then admits an equivariant deterministic choice in a common rule exactly when each profile has an admissible label whose weight occurs exactly once.

If another label has the selected label's weight, their transposition preserves the entire profile and moves the selected label. This contradicts equivariance. Conversely, choose the greatest weight among admissible labels with singleton weight fibers. Finiteness gives a greatest weight, and its singleton fiber gives a unique label. Permuting labels carries the eligible set to the new eligible set and preserves the maximum weight, so it also transports the selected label.

For binary normalized weights with both labels admissible, this recovers the exclusion of the equal-weight pair. In a three-outcome test with weights (2/5, 2/5, 1/5), all labels admissible permits the unique 1/5 label. If admissibility requires a maximum weight, existence instead requires a unique maximum in each profile, which this test lacks.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/FiniteWeightSelector.exists_equivariant_selector_iff`
