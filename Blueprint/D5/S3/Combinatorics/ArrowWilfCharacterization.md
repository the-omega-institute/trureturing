# Fixed Points and the Two Avoidance Conditions

## Abstract

The two patterns are characterized by increasing pairs on opposite sides of a fixed point of the inverse Foata map.

**Theorem 1.1 (Occurrences of the first pattern).**

$$\forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{Contains}\left([1, 2], [(3, 3)], 3, p\right) \Leftrightarrow \left(\exists a \in \mathrm{Nat}, b \in \mathrm{Nat}, f \in \mathrm{Nat},\; a < b \land \left(b < f \land \left(a \in p \land \left(b \in p \land \left(f \in p \land \left(\operatorname{Sublist}\left([a, b], p\right) \land \operatorname{hat}\left(p, f\right) = f\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfCharacterization.contains_twelve_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The first pattern occurs precisely when two entries a and b appear in increasing order below a larger entry f fixed by hat; all three entries belong to the word.

**Theorem 1.2 (Occurrences of the second pattern).**

$$\forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{Contains}\left([2, 3], [(1, 1)], 3, p\right) \Leftrightarrow \left(\exists a \in \mathrm{Nat}, b \in \mathrm{Nat}, f \in \mathrm{Nat},\; f < a \land \left(a < b \land \left(a \in p \land \left(b \in p \land \left(f \in p \land \left(\operatorname{Sublist}\left([a, b], p\right) \land \operatorname{hat}\left(p, f\right) = f\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfCharacterization.contains_twenty_three_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The second pattern occurs precisely when two entries a and b appear in increasing order above a smaller entry f fixed by hat; all three entries belong to the word.

**Theorem 1.3 (Singleton blocks and fixed points).**

$$\forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall f \in \mathrm{Nat},\; \left(\operatorname{Nodup}\left(p\right) \land f \in p\right) \Rightarrow \left(\operatorname{hat}\left(p, f\right) = f \Leftrightarrow \left(\operatorname{IsLtrMax}\left(p, \operatorname{idxOf}\left(p, f\right)\right) \land \left(\operatorname{idxOf}\left(p, f\right) + 1 = \operatorname{length}\left(p\right) \lor f < \operatorname{getD}\left(p, \operatorname{idxOf}\left(p, f\right) + 1, 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfCharacterization.hat_fixed_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For a word with distinct entries containing f, hat fixes f exactly when f starts a left-to-right-maximum block and either ends the word or is followed by an entry larger than f.

**Theorem 1.4 (Either order occurs).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCharacterization.pair_sublist_total`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfCharacterization.pair_sublist_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For two distinct entries of a list without repeated entries, at least one of their two orders occurs as a sublist.

**Theorem 1.5 (The two orders are incompatible).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCharacterization.pair_sublist_asymm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfCharacterization.pair_sublist_asymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A list without repeated entries cannot contain both ordered two-entry sublists on distinct entries.

**Theorem 1.6 (Avoidance below fixed points).**

$$\forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{Nodup}\left(p\right) \Rightarrow \left(\left(\neg \operatorname{Contains}\left([1, 2], [(3, 3)], 3, p\right)\right) \Leftrightarrow \left(\forall f \in \mathrm{Nat},\; \left(f \in p \land \operatorname{hat}\left(p, f\right) = f\right) \Rightarrow \left(\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \left(a < b \land \left(b < f \land \left(a \in p \land b \in p\right)\right)\right) \Rightarrow \operatorname{Sublist}\left([b, a], p\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfCharacterization.avoids_twelve_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A word with distinct entries avoids the first pattern exactly when every pair of entries below each hat-fixed value appears in decreasing order.

**Theorem 1.7 (Avoidance above fixed points).**

$$\forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{Nodup}\left(p\right) \Rightarrow \left(\left(\neg \operatorname{Contains}\left([2, 3], [(1, 1)], 3, p\right)\right) \Leftrightarrow \left(\forall f \in \mathrm{Nat},\; \left(f \in p \land \operatorname{hat}\left(p, f\right) = f\right) \Rightarrow \left(\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \left(f < a \land \left(a < b \land \left(a \in p \land b \in p\right)\right)\right) \Rightarrow \operatorname{Sublist}\left([b, a], p\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfCharacterization.avoids_twenty_three_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

A word with distinct entries avoids the second pattern exactly when every pair of entries above each hat-fixed value appears in decreasing order.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCharacterization.avoids_twelve_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCharacterization.avoids_twenty_three_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCharacterization.contains_twelve_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCharacterization.contains_twenty_three_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCharacterization.hat_fixed_iff`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCharacterization.pair_sublist_asymm`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCharacterization.pair_sublist_total`
- Dependency: [D5/S3/Combinatorics/ArrowWilfDefs](ArrowWilfDefs.md)
