# Literal Zigzag Choices and Balance

## Abstract

The counted objects are Feldman's labelled choices with balance at every nonzero residue, without a closedness or connectivity restriction.

**Definition 1.1 (Six labelled directed forms).**

Lean statement: `D5/S3/Combinatorics/Zigzag/Choices.formPair`

*Formalization.* `D5/S3/Combinatorics/Zigzag/Choices.formPair` (`✓ std3`).

*Citation.* David V. Feldman (2026). *The Missing Zigzag: Cycles of Semitone Trichords and a Conservation Law in Equal Temperament*. URL: <https://arxiv.org/html/2609.26114v1>.

*Commentary.*

Section 5 equation (2) gives I=(1,k-1), II=(k,1-k), III=(-1,k), IV=(k-1,-k), V=(-k,1), and VI=(1-k,-1) in ZMod n. The Form index is retained independently of endpoints: coincident pairs never merge labels. This is a fresh transcription of the paper, compared with the author's formPair, without importing its code or certificates.

**Definition 1.2 (One form per class).**

Lean statement: `D5/S3/Combinatorics/Zigzag/Choices.Choices`

*Formalization.* `D5/S3/Combinatorics/Zigzag/Choices.Choices` (`✓ std3`).

*Citation.* David V. Feldman (2026). *The Missing Zigzag: Cycles of Semitone Trichords and a Conservation Law in Equal Temperament*. URL: <https://arxiv.org/html/2609.26114v1>.

*Commentary.*

For n=3t the index Fin (3t-3) represents exactly k=2 through n-2. The subtype admits only II, III, IV, or V at the first class and retains all six labels thereafter. No endpoint distinctness, step-sum closure, or cyclic order is imposed.

**Definition 1.3 (Balance at nonzero residues).**

Lean statement: `D5/S3/Combinatorics/Zigzag/Choices.Balanced`

*Formalization.* `D5/S3/Combinatorics/Zigzag/Choices.Balanced` (`✓ std3`).

*Citation.* David V. Feldman (2026). *The Missing Zigzag: Cycles of Semitone Trichords and a Conservation Law in Equal Temperament*. URL: <https://arxiv.org/html/2609.26114v1>.

*Commentary.*

The integer imbalance sums outgoing minus incoming incidences of every selected edge. Balanced requires that sum to vanish at each nonzero ZMod residue, leaving the zero residue untested as in the source. It does not assert a closed path, connected graph, Eulerian circuit, or Hamiltonian cycle.

**Definition 1.4 (The actual count a(t)).**

Lean statement: `D5/S3/Combinatorics/Zigzag/Choices.balancedCount`

*Formalization.* `D5/S3/Combinatorics/Zigzag/Choices.balancedCount` (`✓ std3`).

*Citation.* David V. Feldman (2026). *The Missing Zigzag: Cycles of Semitone Trichords and a Conservation Law in Equal Temperament*. URL: <https://arxiv.org/html/2609.26114v1>.

*Commentary.*

This is the cardinality of the finite filter on Choices t satisfying Balanced. Every later path polynomial is linked back to this exact finite set by both parity equivalences; it is never substituted for a proxy count.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/Choices.Balanced`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/Choices.Choices`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/Choices.balancedCount`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/Choices.formPair`
