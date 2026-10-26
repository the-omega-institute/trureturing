# Actual membership words and cyclic boundaries

## Abstract

Actual labelled subsets are equivalent to their Boolean membership functions, and original-host visibility is exactly periodic forbidden-factor avoidance.

**Definition 1.1 (Canonical Boolean labels).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.membershipLabels`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.membershipLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural m, subset X of Z/(3m+2)Z and i in Fin(3m+2), the label at i is the Boolean decision that the vertex represented by i.val belongs to X. The vertex names and origin are fixed.

**Definition 1.2 (The finite membership word).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.membershipWord`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.membershipWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The word is List.ofFn of the canonical membership labels. It lists every original host vertex once in increasing representative order.

**Definition 1.3 (Decode the labels).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.subsetOfLabels`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.subsetOfLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse includes precisely those actual vertices v whose Boolean label at the representative v.val is true.

**Definition 1.4 (Equivalence of actual subsets and labels).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.subsetLabelsEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.subsetLabelsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m, this is an equivalence from Finset(Vertex m) to Fin(3m+2) -> Bool. Its forward map is membershipLabels and its inverse is subsetOfLabels. Both inverse identities are proved using the canonical representatives. There is no quotient by cyclic rotation and no restriction to maximal or independent subsets.

**Theorem 1.5 (Full original host length).**

$$\forall m \in \operatorname{Nat}\left(\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{Vertex}\left(m\right)\right),\; \operatorname{length}\left(\operatorname{membershipWord}\left(m, X\right)\right) = \operatorname{add}\left(\operatorname{mul}\left(3, m\right), 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.membership_word_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m and every actual vertex subset X, the finite membership word has length 3m+2.

**Theorem 1.6 (The complete cyclic boundary bridge).**

$$\forall m \in \operatorname{Nat}\left(\right),\; 1 \le m \Rightarrow \left(\forall X \in \operatorname{Finset}\left(\operatorname{Vertex}\left(m\right)\right),\; \operatorname{Visible}\left(\operatorname{host}\left(m\right), X\right) \Leftrightarrow \operatorname{PeriodicAvoidance}\left(\operatorname{membershipWord}\left(m, X\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.visible_iff_word_periodic_avoidance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m >= 1 and every actual subset X, Visible(host m,X), using shortest paths in the original host, is equivalent to PeriodicAvoidance(membershipWord m X). The proof first characterizes ContainsForbidden in an arbitrary finite indexed block by a start a and positive k with a+3k within the block, selected first and last letters, and selected positions a+1+3j for all j<k. Induction on Triples proves the forward direction; splitting List.ofFn blocks constructs the reverse direction. Repeated words are indexed by the same natural positions interpreted in Z/(3m+2)Z. Every finite forbidden occurrence therefore gives an actual cyclic ForbiddenFactor. Conversely, for an arbitrary cyclic start u and arbitrary positive k, the representative a=u.val and a+3k complete copies provide enough room to realize the whole factor, even across the origin or across many periods. The existing original-host periodic-obstruction theorem then proves the stated equivalence. The supplier's private copies function is related to List.replicate followed by flatten by definitional unfolding and induction; no supplier exposure or assumed boundary alignment is used.

**Theorem 1.7 (The actual index-one count).**

$$\operatorname{count}\left(0\right) = 4$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.count_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original index-one graph has two vertices. Its obstruction predicate is impossible because it would require a positive k at most zero, so every actual subset is visible. An explicit equivalence from the actual Configuration type to all vertex subsets, followed by the finite powerset cardinality, gives exactly four. This is the actual original-host count, independently of any automaton trace.

The consuming count-identification proof may use subsetLabelsEquiv, membership_word_length and visible_iff_word_periodic_avoidance to identify actual labelled configurations with periodic admissible words. The matrix trace counting correspondence and full actual-count generating series are separate obligations; count_zero supplies the actual index-one correction. This module does not assert a complete resolution of A391632.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.count_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.membershipLabels`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.membershipWord`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.membership_word_length`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.subsetLabelsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.subsetOfLabels`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords.visible_iff_word_periodic_avoidance`
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/Andrasfai](Andrasfai.md)
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage](AndrasfaiLanguage.md)
