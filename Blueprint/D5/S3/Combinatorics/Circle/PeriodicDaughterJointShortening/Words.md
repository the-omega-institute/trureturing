# Words for the periodic daughter construction

## Abstract

Ascending daughter blocks and the literal common-cut ear

This helper module defines the physical labels and words used by the existing PeriodicDaughterJointShortening.Construction proof. The word identities organize the lower daughter blocks and shortened top block, while the permutation results provide the exact inventories consumed by daughter_order and the final periodic_daughter_joint_shortening theorem.

**Theorem 1.1 (The old length split).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.length_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.length_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 2≤r, length d r=(r-1)*(d+1)+d, separating the complete lower blocks from the top old block.

**Definition 1.2 (Labels in a regular block).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.regularLabel`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.regularLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

regularLabel d r hr j i is the Fin (length d r) label j.val*(d+1)+i.val for a lower block j and daughter phase i.

**Definition 1.3 (Labels in the top block).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.topLabel`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.topLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

topLabel d r hr i is the Fin (length d r) label (r-1)*(d+1)+i.val for an old top digit.

**Definition 1.4 (Labels in a daughter block).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.daughterLabel`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.daughterLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

daughterLabel d r hr j i is the Fin (length d r+1) label j.val*(d+1)+i.val for daughter block j and phase i.

**Definition 1.5 (The complete lower word).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.lowerWord`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.lowerWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

lowerWord d r hr eta flatMaps eta through regularLabel over List.finRange (r-1). Construction uses it for all complete lower daughter blocks.

**Definition 1.6 (The shortened old word).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.shortenedWord`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.shortenedWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

shortenedWord d r hr tau cut is lowerWord applied to earWord d tau cut, followed by tau mapped through topLabel. This is the old word constructed by Construction.

**Definition 1.7 (The physical common cut).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.commonCut`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.commonCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

commonCut d r cut is (r-1)*(d+1)+cut, the cut after all complete lower blocks and inside the top word.

**Definition 1.8 (The full periodic daughter word).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.daughterWord`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.daughterWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

daughterWord d r hr eta flatMaps eta through daughterLabel over List.finRange r. Construction uses it as the target word after inserting the fresh label.

**Theorem 1.9 (The saturated ear-prefix sum).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_prefix_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_prefix_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For cut≤sigma.length and every h, the mapped sum of (earWord d sigma cut).take h equals the mapped sum of sigma.take (if h≤cut then h else h-1) on castSucc digits, plus the fresh final digit exactly when h>cut. Construction uses this prefix identity in top_block.

**Theorem 1.10 (The complete ear sum).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mapped sum of earWord d tau cut equals the mapped sum of tau castSucc digits plus the final fresh label. Construction uses this identity to compute the top block total.

**Theorem 1.11 (The lower word length).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.lower_length`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.lower_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If tau is a permutation of finRange d, the lower word built from earWord d tau cut has length (r-1)*(d+1).

**Theorem 1.12 (Ear transport across an append).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_after`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_after` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

earWord k (xs++ys) (xs.length+cut) equals xs.map Fin.castSucc ++ earWord k ys cut. This locates the common cut across the lower/top append.

**Theorem 1.13 (The literal global ear identity).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.literal_ear`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.literal_ear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a permutation tau of finRange d, taking the ear at commonCut from shortenedWord gives exactly daughterWord applied to earWord d tau cut. The final theorem uses this equality to identify the daughter ear literally.

**Theorem 1.14 (The daughter product inventory).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.daughter_perm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.daughter_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If eta permutes finRange (d+1), daughterWord d r hr eta permutes finRange (length d r+1). The proof enumerates the injective block-by-phase product, and Construction uses it for the daughter order.

**Theorem 1.15 (The ear inventory).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_perm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If tau permutes finRange d, earWord d tau cut permutes finRange (d+1).

**Definition 1.16 (Removing the globally fresh label).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.removeFresh`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.removeFresh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

removeFresh k maps a Fin (k+1) label below k to the corresponding Fin k label and maps Fin.last k to none.

**Theorem 1.17 (Recovering the old inventory).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.old_perm_of_ear`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.old_perm_of_ear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If earWord k sigma cut permutes finRange (k+1), filtering with removeFresh recovers sigma as a permutation of finRange k. Construction uses this deletion step for the shortened old word.

**Theorem 1.18 (The shortened old permutation).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.shortened_perm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.shortened_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If tau permutes finRange d, shortenedWord d r hr tau cut permutes finRange (length d r). This combines literal_ear, daughter_perm and ear_perm and is consumed by the final construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.commonCut`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.daughterLabel`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.daughterWord`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.daughter_perm`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_after`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_perm`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_prefix_sum`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.ear_sum`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.length_split`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.literal_ear`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.lowerWord`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.lower_length`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.old_perm_of_ear`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.regularLabel`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.removeFresh`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.shortenedWord`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.shortened_perm`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Words.topLabel`
- Dependency: [D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic](Arithmetic.md)
