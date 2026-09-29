# Masks and Initial-Force Anchors at Thirteen Columns

## Abstract

Twenty-six bit positions encode vertices, forts, and six oriented initial-force families.

**Definition 1.1 (The twenty-six vertices).**

$$\mathrm{V13} = \mathrm{Bool}\times \operatorname{Fin}\left(13\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.V13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The false layer is the outer cycle and the true layer is the inner layer, each indexed by Fin 13.

**Definition 1.2 (Column rotation).**

$$\forall r \in \operatorname{Fin}\left(13\right),\; \forall v \in \mathrm{V13},\; \operatorname{rotate13}\left(r, v\right) = (\operatorname{fst}\left(v\right), \operatorname{snd}\left(v\right) - r)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.rotate13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Rotation subtracts the chosen column from the index in each layer.

**Definition 1.3 (Bit position of a vertex).**

$$\forall v \in \mathrm{V13},\; \operatorname{code13}\left(v\right) = \operatorname{if}\left(\operatorname{fst}\left(v\right) = \mathrm{true}, 13 + \operatorname{val}\left(\operatorname{snd}\left(v\right)\right), \operatorname{val}\left(\operatorname{snd}\left(v\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.code13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Outer vertices occupy bits zero through twelve; inner vertices occupy bits thirteen through twenty-five.

**Definition 1.4 (Decode a vertex mask).**

$$\forall m \in \mathrm{Nat},\; \operatorname{maskSet13}\left(m\right) = \{ v \in \mathrm{V13}| \operatorname{testBit}\left(m, \operatorname{code13}\left(v\right)\right) = \mathrm{true}\} $$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.maskSet13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A vertex belongs to the decoded set exactly when its corresponding bit is set.

**Definition 1.5 (The three neighbors).**

$$\forall v \in \mathrm{V13},\; \operatorname{neighbors13}\left(v\right) = \operatorname{if}\left(\operatorname{fst}\left(v\right) = \mathrm{true}, \left\{(\mathrm{false}, \operatorname{snd}\left(v\right)), (\mathrm{true}, \operatorname{snd}\left(v\right) + 3), (\mathrm{true}, \operatorname{snd}\left(v\right) - 3)\right\}, \left\{(\mathrm{true}, \operatorname{snd}\left(v\right)), (\mathrm{false}, \operatorname{snd}\left(v\right) + 1), (\mathrm{false}, \operatorname{snd}\left(v\right) - 1)\right\}\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.neighbors13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Each vertex has its spoke mate and the two cyclic neighbors at step one in the outer layer or step three in the inner layer.

**Definition 1.6 (Numeric neighbor positions).**

$$\forall i \in \mathrm{Nat},\; \operatorname{neighborCodes13}\left(i\right) = \operatorname{if}\left(i < 13, [\left(i + 12\right) \bmod 13, \left(i + 1\right) \bmod 13, 13 + i], [i - 13, 13 + \left(i - 13 + 10\right) \bmod 13, 13 + \left(i - 13 + 3\right) \bmod 13]\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.neighborCodes13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The arithmetic neighbor list uses residues modulo thirteen and the same two-layer bit convention.

**Definition 1.7 (Finite fort predicate).**

$$\forall m \in \mathrm{Nat},\; \operatorname{fortOK}\left(m\right) = \mathrm{true} \Leftrightarrow \left(0 < m \land \left(m < 2^{26} \land \left(\forall i \in \mathrm{Nat},\; i < 26 \Rightarrow \left(\operatorname{testBit}\left(m, i\right) = \mathrm{true} \lor \operatorname{countP}\left(\operatorname{neighborCodes13}\left(i\right), (\lambda j:\mathrm{Nat}, \operatorname{testBit}\left(m, j\right))\right) \ne 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.fortOK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A valid mask is nonzero and below two to the twenty-sixth power. Every absent vertex has a number of neighbors in the mask different from one.

**Definition 1.8 (Disjoint vertex masks).**

$$\forall s \in \mathrm{Nat},\; \forall f \in \mathrm{Nat},\; \operatorname{disjointOK}\left(s, f\right) = \mathrm{true} \Leftrightarrow \left(s < 2^{26} \land \left(f < 2^{26} \land \operatorname{bitwise}\left(\mathrm{and}, s, f\right) = 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.disjointOK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Both masks fit in twenty-six bits and their bitwise intersection is zero.

**Definition 1.9 (Candidate and fort pair).**

$$\forall row \in \mathrm{Nat}\times \mathrm{Nat},\; \operatorname{rowOK}\left(row\right) = \mathrm{true} \Leftrightarrow \left(\operatorname{fortOK}\left(\operatorname{snd}\left(row\right)\right) = \mathrm{true} \land \operatorname{disjointOK}\left(\operatorname{fst}\left(row\right), \operatorname{snd}\left(row\right)\right) = \mathrm{true}\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.rowOK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A row pairs a candidate mask with a valid fort mask disjoint from it.

**Definition 1.10 (Population of the low bits).**

$$\forall m \in \mathrm{Nat},\; \operatorname{bitCount26}\left(m\right) = \operatorname{card}\left(\{ i \in \mathrm{Nat}| i < 26 \land \operatorname{testBit}\left(m, i\right) = \mathrm{true}\} \right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.bitCount26` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Count the set bits at positions zero through twenty-five.

**Definition 1.11 (Six oriented first forces).**

$$\operatorname{univ}\left(\mathrm{Anchor13}\right) = \left\{\mathrm{outerSpoke}, \mathrm{outerNext}, \mathrm{outerPrev}, \mathrm{innerSpoke}, \mathrm{innerNext}, \mathrm{innerPrev}\right\}$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.Anchor13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The constructors distinguish an outer or inner source and a spoke, forward, or backward target.

**Definition 1.12 (Finite enumeration of the anchors).**

$$\operatorname{elems}\left(\mathrm{instFintypeAnchor13}\right) = \left\{\mathrm{outerSpoke}, \mathrm{outerNext}, \mathrm{outerPrev}, \mathrm{innerSpoke}, \mathrm{innerNext}, \mathrm{innerPrev}\right\}$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.instFintypeAnchor13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The finite-type structure enumerates exactly the six constructors of Anchor13.

**Definition 1.13 (The list of anchors).**

$$\mathrm{anchors13} = [\mathrm{outerSpoke}, \mathrm{outerNext}, \mathrm{outerPrev}, \mathrm{innerSpoke}, \mathrm{innerNext}, \mathrm{innerPrev}]$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.anchors13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The list contains the six oriented first-force anchors in the displayed order.

**Definition 1.14 (Three required black vertices).**

$$\operatorname{anchorRequired}\left(\mathrm{outerSpoke}\right) = \left\{(\mathrm{false}, 12), (\mathrm{false}, 0), (\mathrm{false}, 1)\right\} \land \left(\operatorname{anchorRequired}\left(\mathrm{outerNext}\right) = \left\{(\mathrm{false}, 12), (\mathrm{false}, 0), (\mathrm{true}, 0)\right\} \land \left(\operatorname{anchorRequired}\left(\mathrm{outerPrev}\right) = \left\{(\mathrm{false}, 1), (\mathrm{false}, 0), (\mathrm{true}, 0)\right\} \land \left(\operatorname{anchorRequired}\left(\mathrm{innerSpoke}\right) = \left\{(\mathrm{true}, 10), (\mathrm{true}, 0), (\mathrm{true}, 3)\right\} \land \left(\operatorname{anchorRequired}\left(\mathrm{innerNext}\right) = \left\{(\mathrm{true}, 10), (\mathrm{true}, 0), (\mathrm{false}, 0)\right\} \land \operatorname{anchorRequired}\left(\mathrm{innerPrev}\right) = \left\{(\mathrm{true}, 3), (\mathrm{true}, 0), (\mathrm{false}, 0)\right\}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.anchorRequired` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For each anchor, the required vertices are the source at column zero and its two neighbors other than the target.

**Definition 1.15 (The white target).**

$$\operatorname{anchorTarget}\left(\mathrm{outerSpoke}\right) = (\mathrm{true}, 0) \land \left(\operatorname{anchorTarget}\left(\mathrm{outerNext}\right) = (\mathrm{false}, 1) \land \left(\operatorname{anchorTarget}\left(\mathrm{outerPrev}\right) = (\mathrm{false}, 12) \land \left(\operatorname{anchorTarget}\left(\mathrm{innerSpoke}\right) = (\mathrm{false}, 0) \land \left(\operatorname{anchorTarget}\left(\mathrm{innerNext}\right) = (\mathrm{true}, 3) \land \operatorname{anchorTarget}\left(\mathrm{innerPrev}\right) = (\mathrm{true}, 10)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.anchorTarget` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The target is the remaining neighbor in the oriented force, with all column indices taken modulo thirteen.

**Definition 1.16 (Seven vertices extending an anchor).**

$$\forall a \in \mathrm{Anchor13},\; \forall m \in \mathrm{Nat},\; \operatorname{candidateShapeOK}\left(a, m\right) = \mathrm{true} \Leftrightarrow \left(m < 2^{26} \land \left(\operatorname{bitCount26}\left(m\right) = 7 \land \left(\left(\forall v \in \mathrm{V13},\; v \in \operatorname{anchorRequired}\left(a\right) \Rightarrow \operatorname{testBit}\left(m, \operatorname{code13}\left(v\right)\right) = \mathrm{true}\right) \land \left(\neg \operatorname{testBit}\left(m, \operatorname{code13}\left(\operatorname{anchorTarget}\left(a\right)\right)\right) = \mathrm{true}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.candidateShapeOK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A candidate has seven vertices, contains the three required vertices, and omits the white target.

**Definition 1.17 (Increasing candidate masks).**

$$\forall rows \in \operatorname{List}\left(\mathrm{Nat}\times \mathrm{Nat}\right),\; \operatorname{StrictKeys}\left(rows\right) = \mathrm{true} \Leftrightarrow \left(\forall i \in \mathrm{Nat},\; i + 1 < \operatorname{length}\left(rows\right) \Rightarrow \operatorname{fst}\left(rows[i]\right) < \operatorname{fst}\left(rows[i + 1]\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.StrictKeys` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Successive row keys are strictly increasing.

**Definition 1.18 (Size and order of an anchor family).**

$$\forall rows \in \operatorname{List}\left(\mathrm{Nat}\times \mathrm{Nat}\right),\; \operatorname{familyOrderOK}\left(rows\right) = \mathrm{true} \Leftrightarrow \left(\operatorname{length}\left(rows\right) = 7315 \land \operatorname{StrictKeys}\left(rows\right) = \mathrm{true}\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.familyOrderOK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

An ordered family has 7315 rows and strictly increasing candidate masks.

**Definition 1.19 (Consecutive chunks of rows).**

$$\forall a \in \mathrm{Anchor13},\; \forall chunks \in \operatorname{List}\left(\operatorname{List}\left(\mathrm{Nat}\times \mathrm{Nat}\right)\right),\; \forall start \in \mathrm{Nat},\; \forall len \in \mathrm{Nat},\; \operatorname{chunkBlockOK}\left(a, chunks, start, len\right) = \mathrm{true} \Leftrightarrow \left(\forall j \in \mathrm{Nat},\; j < len \Rightarrow \left(\forall row \in \mathrm{Nat}\times \mathrm{Nat},\; row \in \operatorname{getD}\left(chunks, start + j, []\right) \Rightarrow \left(\operatorname{candidateShapeOK}\left(a, \operatorname{fst}\left(row\right)\right) = \mathrm{true} \land \operatorname{rowOK}\left(row\right) = \mathrm{true}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.chunkBlockOK` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Every row in the selected consecutive chunks has the specified anchor shape and a disjoint fort. A chunk index beyond the list denotes the empty list.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.Anchor13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.StrictKeys`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.V13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.anchorRequired`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.anchorTarget`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.anchors13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.bitCount26`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.candidateShapeOK`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.chunkBlockOK`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.code13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.disjointOK`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.familyOrderOK`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.fortOK`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.instFintypeAnchor13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.maskSet13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.neighborCodes13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.neighbors13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.rotate13`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.rowOK`
