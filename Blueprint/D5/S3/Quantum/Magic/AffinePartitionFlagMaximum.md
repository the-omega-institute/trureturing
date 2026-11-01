# The affine partition flag maximum

## Abstract

The flag partition maximizes the squared sizes of affine parts outside the origin.

**Definition 1.1 (Affine partitions of the punctured vector space).**

$$\forall (p: \mathbb{N}), [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)] \forall (n: \mathbb{N}), (\forall (parts: \operatorname{Finset}\left(\operatorname{AffineSubspace}\left(\operatorname{ZMod}\left(p\right), \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right)\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{isAffinePartition}\left(p, n, parts\right) = \left((\forall (k: \operatorname{AffineSubspace}\left(\operatorname{ZMod}\left(p\right), \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right)), ((k \in parts) \Rightarrow (\operatorname{Set}.\operatorname{Nonempty}\left((k: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right))\right)))) \land ((\forall (k: \operatorname{AffineSubspace}\left(\operatorname{ZMod}\left(p\right), \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right)), ((k \in parts) \Rightarrow (\forall (l: \operatorname{AffineSubspace}\left(\operatorname{ZMod}\left(p\right), \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right)), ((l \in parts) \Rightarrow ((k \ne l) \Rightarrow (\operatorname{Disjoint}\left((k: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right)), (l: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right))\right))))))) \land (\forall (v: \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)), ((v \ne (0: \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right))) \Leftrightarrow (\exists (k: \operatorname{AffineSubspace}\left(\operatorname{ZMod}\left(p\right), \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right)), ((k \in parts) \land (v \in (k: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right))))))))\right)))$$

*Formalization.* `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.isAffinePartition` (`✓ std3`).

*Citation.* Arne Heimendahl; Markus Heinrich; David Gross (2022). *The axiomatic and the operational approaches to resource theories of magic do not coincide*. DOI: [10.1063/5.0085774](https://doi.org/10.1063/5.0085774). URL: <https://arxiv.org/abs/2011.11651v3>.

*Commentary.*

A finite family of affine subspaces is an affine partition when every part is nonempty, distinct parts are disjoint, and a vector is nonzero exactly when it belongs to one of the parts. This is the partition condition in the source's stabiliser-operation lemma (lines 986–994).

**Definition 1.2 (The squared-cardinality objective).**

$$\forall (p: \mathbb{N}), [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)] \forall (n: \mathbb{N}), (\forall (parts: \operatorname{Finset}\left(\operatorname{AffineSubspace}\left(\operatorname{ZMod}\left(p\right), \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right)\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{sqSum}\left(p, n, parts\right) = \sum_{k \in parts} (\operatorname{Nat}.\operatorname{card}\left(\operatorname{CoeSort}.\operatorname{coe}\left((k: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right))\right)\right)^{2})))$$

*Formalization.* `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.sqSum` (`✓ std3`).

*Citation.* Arne Heimendahl; Markus Heinrich; David Gross (2022). *The axiomatic and the operational approaches to resource theories of magic do not coincide*. DOI: [10.1063/5.0085774](https://doi.org/10.1063/5.0085774). URL: <https://arxiv.org/abs/2011.11651v3>.

*Commentary.*

sqSum adds the squares of the cardinalities of the affine parts. It is the quantity appearing in the source's overlap bound (lines 1209–1217).

**Definition 1.3 (A coordinate flag cell).**

$$\forall (p: \mathbb{N}), [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)] \forall (n: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (x: \operatorname{ZMod}\left(p\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagCell}\left(p, n, i, x\right): \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right)) = \{v: \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right) \mid (\forall (j: \operatorname{Fin}\left(n\right)), ((j < i) \Rightarrow (v\left(j\right) = (0: \operatorname{ZMod}\left(p\right))))) \land (v\left(i\right) = x)\})))$$

*Formalization.* `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.flagCell` (`✓ std3`).

*Citation.* Arne Heimendahl; Markus Heinrich; David Gross (2022). *The axiomatic and the operational approaches to resource theories of magic do not coincide*. DOI: [10.1063/5.0085774](https://doi.org/10.1063/5.0085774). URL: <https://arxiv.org/abs/2011.11651v3>.

*Commentary.*

For an index i and a nonzero or zero coordinate value x, flagCell p n i x consists of vectors whose coordinates before i vanish and whose i-th coordinate equals x. It is the affine tail described by the source's first-nonzero-coordinate construction (lines 1219–1232).

**Definition 1.4 (The partition by first nonzero coordinate).**

$$\forall (p: \mathbb{N}), [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)] \forall (n: \mathbb{N}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagPartition}\left(p, n\right) = \operatorname{Finset}.\operatorname{image}\left((\Lambda (a: \operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Subtype}\left((\Lambda (x: \operatorname{ZMod}\left(p\right)) \mapsto x \ne (0: \operatorname{ZMod}\left(p\right)))\right)\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagCell}\left(p, n, \operatorname{Prod}.\operatorname{fst}\left(a\right), \operatorname{Subtype}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(a\right)\right)\right)), \operatorname{Finset}.\operatorname{univ}\left(\right)\right))$$

*Formalization.* `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.flagPartition` (`✓ std3`).

*Citation.* Arne Heimendahl; Markus Heinrich; David Gross (2022). *The axiomatic and the operational approaches to resource theories of magic do not coincide*. DOI: [10.1063/5.0085774](https://doi.org/10.1063/5.0085774). URL: <https://arxiv.org/abs/2011.11651v3>.

*Commentary.*

flagPartition is the image of all pairs (i,x) with i in Fin n and x a nonzero element of ZMod p under the flag-cell construction. It encodes the measurement procedure and induced partition in the source (lines 1219–1232).

**Definition 1.5 (The value of the flag partition).**

$$\forall (p: \mathbb{N}), (\forall (n: \mathbb{N}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagValue}\left(p, n\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n\right)} (\left(p - 1\right) \cdot p^{2 \cdot k})))$$

*Formalization.* `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.flagValue` (`✓ std3`).

*Citation.* Arne Heimendahl; Markus Heinrich; David Gross (2022). *The axiomatic and the operational approaches to resource theories of magic do not coincide*. DOI: [10.1063/5.0085774](https://doi.org/10.1063/5.0085774). URL: <https://arxiv.org/abs/2011.11651v3>.

*Commentary.*

flagValue p n is the finite sum ∑ₖ₍₀≤k<n₎ (p−1)p^(2k), the squared-cardinality value stated for the flag partition in the source (lines 1233–1237).

**Definition 1.6 (The flag partition maximum conjecture).**

$$\forall (p: \mathbb{N}), [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)] \forall (n: \mathbb{N}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{isAffinePartition}\left(p, n, \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagPartition}\left(p, n\right)\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{sqSum}\left(p, n, \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagPartition}\left(p, n\right)\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagValue}\left(p, n\right)) \land (\forall (parts: \operatorname{Finset}\left(\operatorname{AffineSubspace}\left(\operatorname{ZMod}\left(p\right), \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right)\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{isAffinePartition}\left(p, n, parts\right)) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{sqSum}\left(p, n, parts\right) \le \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagValue}\left(p, n\right))))))$$

*Formalization.* `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.claim` (`✓ std3`).

*Citation.* Arne Heimendahl; Markus Heinrich; David Gross (2022). *The axiomatic and the operational approaches to resource theories of magic do not coincide*. DOI: [10.1063/5.0085774](https://doi.org/10.1063/5.0085774). URL: <https://arxiv.org/abs/2011.11651v3>.

*Commentary.*

For every prime p and natural n, the flag cells form an affine partition of the nonzero vectors, their squared-cardinality sum is flagValue, and every affine partition has no larger squared-cardinality sum. This is the source's maximising-measurement conjecture under the formal reading that all affine partitions are admitted (lines 1215–1232).

**Theorem 1.7 (The affine partition flag maximum is proved).**

$$\forall (p: \mathbb{N}), [\operatorname{Fact}\left(\operatorname{Nat}.\operatorname{Prime}\left(p\right)\right)] \forall (n: \mathbb{N}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{isAffinePartition}\left(p, n, \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagPartition}\left(p, n\right)\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{sqSum}\left(p, n, \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagPartition}\left(p, n\right)\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagValue}\left(p, n\right)) \land (\forall (parts: \operatorname{Finset}\left(\operatorname{AffineSubspace}\left(\operatorname{ZMod}\left(p\right), \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(p\right)\right)\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{isAffinePartition}\left(p, n, parts\right)) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{sqSum}\left(p, n, parts\right) \le \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Magic}.\operatorname{AffinePartitionFlagMaximum}.\operatorname{flagValue}\left(p, n\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.result` (`✓ std3`). ∎

*Resolves.* `Problems/heimendahl-heinrich-gross-2022-affine-partition-flag` (proved) by `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"heimendahl-heinrich-gross-2022-affine-partition-flag","declaration_gid":"D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arne Heimendahl; Markus Heinrich; David Gross (2022). *The axiomatic and the operational approaches to resource theories of magic do not coincide*. DOI: [10.1063/5.0085774](https://doi.org/10.1063/5.0085774). URL: <https://arxiv.org/abs/2011.11651v3>.

*Commentary.*

The proof first identifies the cardinality of every nonempty affine part with p raised to the finrank of its direction, and uses disjointness and coverage to show that the part sizes sum to p^n−1. It then introduces a digit potential formed from the base-p digits of s. Its step, affine, and one-unit identities yield the power inequality p^(2k) plus the potential of s−p^k is at most the potential of s whenever p^k ≤ s. Induction over a finite family of powers of p gives the squared-size bound by the potential of the total size, and induction on n evaluates the potential at p^n−1 as flagValue p n.

The flag-cell center Pi.single i x proves nonemptiness; the least nonzero coordinate of a vector gives the unique flag index, proving disjointness and covering exactly the nonzero vectors. Each cell is the space of extensions of Pi.single i x on the record Finset.Iic i. The general record_extension_card theorem gives its cardinality p^(n−1−i). Summing over i and over the p−1 nonzero coordinate values gives flagValue. Combining these facts with the digit-potential bound proves claim (arXiv TeX lines 1219–1245).

## References

- Truth anchor: `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.claim`
- Truth anchor: `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.flagCell`
- Truth anchor: `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.flagPartition`
- Truth anchor: `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.flagValue`
- Truth anchor: `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.isAffinePartition`
- Truth anchor: `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.result`
- Truth anchor: `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.sqSum`
- Dependency: [D5/S0/Diagonal/RecordExtensionCount](../../../S0/Diagonal/RecordExtensionCount.md)
