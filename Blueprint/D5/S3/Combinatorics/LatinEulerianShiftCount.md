# Residue Comparisons After Swapping Zero and One

## Abstract

Swapping the two least residues changes only the two endpoint comparisons in a cyclic shift.

**Definition 1.1 (Residue transposition).**

$$\forall x \in \mathrm{Nat},\; \operatorname{swap01}\left(x\right) = \operatorname{if}\left(x = 0, 1, \operatorname{if}\left(x = 1, 0, x\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianShiftCount.swap01` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The map exchanges zero and one and fixes every other natural residue.

**Theorem 1.2 (Shifted comparison characterization).**

$$\forall n \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall x \in \mathrm{Nat},\; \left(3 \le n \land \left(0 < d \land \left(d < n \land x < n\right)\right)\right) \Rightarrow \left(\operatorname{swap01}\left(x\right) < \operatorname{swap01}\left(\operatorname{mod}\left(x + d, n\right)\right) \Leftrightarrow \left(\left(x < n - d \land \left(\neg \left(d = 1 \land x = 0\right)\right)\right) \lor \left(d = n - 1 \land x = 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinEulerianShiftCount.shifted_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

For a nonzero shift smaller than the modulus, the swapped comparison holds on the ordinary nonwrapping interval, except for the zero to one step, together with the one to zero endpoint when the shift is the predecessor residue.

**Definition 1.3 (Shifted ascent count).**

$$\forall n \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \operatorname{shiftedAscents}\left(n, d\right) = \operatorname{card}\left(\{x \in \mathrm{Nat}| x < n \land \operatorname{swap01}\left(x\right) < \operatorname{swap01}\left(\operatorname{mod}\left(x + d, n\right)\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianShiftCount.shiftedAscents` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

Count the residues whose shifted pair is increasing after the transposition.

**Theorem 1.4 (Shifted ascent formula).**

$$\forall n \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \left(3 \le n \land \left(0 < d \land d < n\right)\right) \Rightarrow \operatorname{shiftedAscents}\left(n, d\right) + \operatorname{if}\left(d = 1, 1, 0\right) = n - d + \operatorname{if}\left(d = n - 1, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinEulerianShiftCount.shifted_ascent_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The count is n minus d, with one correction when d is one and one correction when d is n minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/LatinEulerianShiftCount.shiftedAscents`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianShiftCount.shifted_ascent_count`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianShiftCount.shifted_comparison`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianShiftCount.swap01`
- Dependency: [D5/S3/Combinatorics/LatinEulerianDefs](LatinEulerianDefs.md)
