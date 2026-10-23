# GenericLieLengthConstruction

## Abstract

A three-colour anchored binary heap produces a logarithmic-length generating pair.

**Definition 1.1 (heapColor).**

$$\forall (v : \mathbb{N}) , \operatorname{heapColor} v = \operatorname{if} v \leq 1 \operatorname{then} 0 \operatorname{else} \operatorname{Nat} . \operatorname{mod} (\operatorname{heapColor} (\operatorname{Nat} . \operatorname{div} v 2) + (\operatorname{if} \operatorname{Nat} . \operatorname{mod} v 2 = 0 \operatorname{then} 1 \operatorname{else} 2)) 3$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.heapColor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three colours distinguish a parent from each child and distinguish its two children. Nat.div and Nat.mod are natural quotient and remainder.

**Definition 1.2 (energy).**

$$\forall (v : \mathbb{N}) , \operatorname{energy} v = \operatorname{if} v = 0 \operatorname{then} 7 \operatorname{else} \operatorname{if} \operatorname{heapColor} v = 0 \operatorname{then} 0 \operatorname{else} \operatorname{if} \operatorname{heapColor} v = 1 \operatorname{then} 1 \operatorname{else} 3$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The distinguished zero vertex has energy 7; the three heap colours have energies 0, 1 and 3.

**Definition 1.3 (heapEdge).**

$$\forall (u v : \mathbb{N}) , \operatorname{heapEdge} u v \iff ((u = 0 \land v = 1) \lor (u = 1 \land v = 0) \lor (2 \leq u \land \operatorname{Nat} . \operatorname{div} u 2 = v) \lor (2 \leq v \land \operatorname{Nat} . \operatorname{div} v 2 = u))$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.heapEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The anchor edge joins zero to one, and every other edge joins a positive vertex to its binary-heap parent.

**Definition 1.4 (meanEnergy).**

$$\forall (n : \mathbb{N}) , \operatorname{meanEnergy} n = (\sum_{v : \operatorname{Fin} (n + 2)} (\operatorname{energy} v . \operatorname{val} : \mathbb{C})) / (n + 2 : \mathbb{C})$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.meanEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtracting the mean makes the diagonal trace zero.

**Definition 1.5 (centeredEnergy).**

$$\forall (n : \mathbb{N}) (v : \operatorname{Fin} (n + 2)) , \operatorname{centeredEnergy} n v = (\operatorname{energy} v . \operatorname{val} : \mathbb{C}) - \operatorname{meanEnergy} n$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.centeredEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These centered complex entries are real-valued.

**Definition 1.6 (A).**

$$\forall (n : \mathbb{N}) , \operatorname{A} n = \operatorname{Matrix} . \operatorname{diagonal} (\operatorname{centeredEnergy} n)$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first Hermitian generator is the centered energy diagonal.

**Definition 1.7 (B).**

$$\forall (n : \mathbb{N}) , \operatorname{B} n = (\operatorname{SimpleGraph} . \operatorname{fromRel} (\operatorname{fun} (i j : \operatorname{Fin} (n + 2)) \mapsto \operatorname{heapEdge} i . \operatorname{val} j . \operatorname{val})) . \operatorname{adjMatrix} \mathbb{C}$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second Hermitian generator is the symmetric adjacency matrix of the anchored heap.

**Definition 1.8 (gen).**

$$\forall (n : \mathbb{N}) , \operatorname{gen} n = ! [ \operatorname{A} n , \operatorname{B} n ]$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.gen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two-entry vector lists the diagonal and adjacency generators.

**Definition 1.9 (iGen).**

$$\forall (n : \mathbb{N}) (i : \operatorname{Fin} 2) , \operatorname{iGen} n i = \operatorname{HSMul} . \operatorname{hSMul} \operatorname{Complex} . \operatorname{I} (\operatorname{gen} n i)$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.iGen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplication by the complex imaginary unit gives traceless skew-Hermitian generators.

**Theorem 1.10 (anchored_units_mem).**

$$\forall (n : \mathbb{N}) (v : \operatorname{Fin} (n + 2)) , 1 \leq v . \operatorname{val} \to (\operatorname{Matrix} . \operatorname{single} v 0 (1 : \mathbb{C}) \in \operatorname{rightSpan} (K := \mathbb{C}) (\operatorname{gen} n) (8 * \operatorname{Nat} . \operatorname{size} v . \operatorname{val}) \land \operatorname{Matrix} . \operatorname{single} 0 v (1 : \mathbb{C}) \in \operatorname{rightSpan} (K := \mathbb{C}) (\operatorname{gen} n) (8 * \operatorname{Nat} . \operatorname{size} v . \operatorname{val}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.anchored_units_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Degree-seven Lagrange polynomials in the diagonal adjoint select gaps from {−7,−3,−2,−1,1,2,3,7}. The anchor units then propagate to both children in eight additional letters per level. Nat.size is the binary length, zero at zero and 1 + Nat.log 2 v for positive v.

**Definition 1.11 (suLieRing).**

$$\forall (n : \mathbb{N}) , \operatorname{suLieRing} n = \operatorname{inferInstanceAs} (\operatorname{LieRing} (\operatorname{suLie} n))$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.suLieRing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Lie-ring structure on the real submodule is the one on the corresponding Lie subalgebra.

**Definition 1.12 (suLieAlgebra).**

$$\forall (n : \mathbb{N}) , \operatorname{suLieAlgebra} n = \operatorname{inferInstanceAs} (\operatorname{LieAlgebra} \mathbb{R} (\operatorname{suLie} n))$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.suLieAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real Lie-algebra structure is inherited from the same Lie subalgebra.

**Definition 1.13 (compactPair).**

$$\forall (n : \mathbb{N}) (i : \operatorname{Fin} 2) , (compactPair n i : \operatorname{Matrix} (\operatorname{Fin} (n + 2)) (\operatorname{Fin} (n + 2)) \mathbb{C}) = \operatorname{iGen} n i$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.compactPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

compactPair has type Fin 2 → suSet (n + 2), with value iGen n i. Its subtype property is exactly traceless skew-Hermiticity.

**Theorem 1.14 (rightSpan_map).**

$$\forall (I K M N : \operatorname{Type} *) [ \operatorname{CommRing} K ] [ \operatorname{LieRing} M ] [ \operatorname{LieAlgebra} K M ] [ \operatorname{LieRing} N ] [ \operatorname{LieAlgebra} K N ] (f : \operatorname{LieHom} K M N) (S : I \to M) (L : \mathbb{N}) , \operatorname{Submodule} . \operatorname{map} f . \operatorname{toLinearMap} (\operatorname{rightSpan} (K := K) S L) = \operatorname{rightSpan} (K := K) (\operatorname{fun} (i : I) \mapsto f (S i)) L$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.rightSpan_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Lie homomorphism commutes with every word evaluation and hence with its span.

**Theorem 1.15 (compactPair_span_top).**

$$\forall (n : \mathbb{N}) , \operatorname{rightSpan} (K := \mathbb{R}) (\operatorname{compactPair} n) (16 * (1 + \operatorname{Nat} . \operatorname{log} 2 (n + 1))) = \operatorname{Top}.\operatorname{top}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.compactPair_span_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bracketing the anchored matrix units gives all adjusted units, which span the trace kernel. Scaling by the imaginary unit and taking skew-adjoint parts gives the whole real subalgebra.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.A`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.B`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.anchored_units_mem`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.centeredEnergy`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.compactPair`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.compactPair_span_top`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.energy`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.gen`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.heapColor`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.heapEdge`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.iGen`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.meanEnergy`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.rightSpan_map`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.suLieAlgebra`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLengthConstruction.suLieRing`
- Dependency: [D5/S3/Quantum/Algebra/GenericLieLengthFiltration](GenericLieLengthFiltration.md)
