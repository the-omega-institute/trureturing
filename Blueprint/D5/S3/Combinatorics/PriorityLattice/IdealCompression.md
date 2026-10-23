# IdealCompression

## Abstract

Priority-forest interval structure and counting.

**Definition 1.1 (CodeClosed).**

$$\forall (\operatorname{k} : \operatorname{Nat}) (\operatorname{t} : ((\operatorname{v} : \operatorname{Fin} \operatorname{k}) \to \operatorname{Fin} (\operatorname{val}(\operatorname{v}) + 1))) (\operatorname{s} : \operatorname{Finset} (\operatorname{Fin} \operatorname{k})) , \operatorname{CodeClosed} \operatorname{t} \operatorname{s} \iff \forall (\operatorname{v} : \operatorname{Fin} \operatorname{k}) , \operatorname{v} \in \operatorname{s} \to \forall (\operatorname{w} : \operatorname{Fin} \operatorname{k}) , \operatorname{val}((\operatorname{t} \operatorname{v})) \leq \operatorname{val}(\operatorname{w}) \to \operatorname{w} \leq \operatorname{v} \to \operatorname{w} \in \operatorname{s}$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.CodeClosed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

A subset is CodeClosed when it contains every index between the parent code val(t v) and each of its members v.

**Definition 1.2 (IntervalForest / supportParent).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{v} : \operatorname{CoeSort.coe}\left(\operatorname{ForestCovers.IntervalForest.support} \operatorname{P}\right)) , \operatorname{supportParent} \operatorname{P} \operatorname{v} = \operatorname{Exists.choose} (\operatorname{Option.\left(\left(ne_{none}\right)_{iff}\right)_{exists}} ' . \operatorname{mp} ((\operatorname{ForestCovers.IntervalForest.mem_{support}} \operatorname{P} \operatorname{val}(\operatorname{v})) . \operatorname{mp} \operatorname{v.property}))$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.supportParent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The chosen parent is extracted from the existence of a parent for each support member; the displayed value projection passes that member to the forest parent function.

**Theorem 1.3 (IntervalForest / supportParent_spec).**

$$\forall \{\operatorname{n} : \mathbb{N}\} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{v} : \operatorname{CoeSort.coe}\left(\operatorname{ForestCovers.IntervalForest.support} \operatorname{P}\right)) , \operatorname{P.parent} \operatorname{val}(\operatorname{v}) = \operatorname{some} (\operatorname{IdealCompression.IntervalForest.supportParent} \operatorname{P} \operatorname{v})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IdealCompression.supportParent_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Definition 1.4 (IntervalForest / firstNeeded).**

$$\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{v} : \operatorname{CoeSort.coe}\left(\operatorname{ForestCovers.IntervalForest.support} \operatorname{P}\right)) , \operatorname{val}((\operatorname{firstNeeded} \operatorname{P} \operatorname{v})) = \operatorname{val}((\operatorname{supportParent} \operatorname{P} \operatorname{v})) + 1$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.firstNeeded` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

firstNeeded has value val(supportParent P v) + 1; increasing parents place this label within Fin (n + 1).

**Definition 1.5 (IntervalForest / firstIndex).**

$$\forall (\operatorname{n} \operatorname{k} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{h} : \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = \operatorname{k}) (\operatorname{i} : \operatorname{Fin} \operatorname{k}) , \operatorname{val}((\operatorname{Finset.orderIsoOfFin} (\operatorname{ForestCovers.IntervalForest.support} \operatorname{P}) \operatorname{h} (\operatorname{firstIndex} \operatorname{P} \operatorname{h} \operatorname{i}))) = \operatorname{firstNeeded} \operatorname{P} (\operatorname{Finset.orderIsoOfFin} (\operatorname{ForestCovers.IntervalForest.support} \operatorname{P}) \operatorname{h} \operatorname{i})$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.firstIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

firstIndex sends i to the index, under Finset.orderIsoOfFin, of firstNeeded P applied to the support label at index i.

**Definition 1.6 (IntervalForest / compressCode).**

$$\forall (\operatorname{n} \operatorname{k} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{h} : \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = \operatorname{k}) (\operatorname{i} : \operatorname{Fin} \operatorname{k}) , \operatorname{val}((\operatorname{compressCode} \operatorname{P} \operatorname{h} \operatorname{i})) = \operatorname{val}((\operatorname{firstIndex} \operatorname{P} \operatorname{h} \operatorname{i}))$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.compressCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

compressCode sends i to the finite code with value val(firstIndex P h i). The bound on firstIndex makes this value an element of Fin (val(i) + 1).

**Definition 1.7 (IntervalForest / idealCodeOrderIso).**

$$\forall (\operatorname{n} \operatorname{k} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{h} : \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = \operatorname{k}) (\operatorname{Q} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{hQ} : \operatorname{Q} \leq \operatorname{P}) , \operatorname{val}((\operatorname{idealCodeOrderIso} \operatorname{P} \operatorname{h} (\operatorname{Subtype.mk} (\operatorname{Q} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} \operatorname{n})) (\operatorname{WithTop.\left(coe_{le}\right)_{coe}.mpr} \operatorname{hQ})))) = \operatorname{Finset.univ.filter} (\operatorname{fun} (\operatorname{i} : \operatorname{Fin} \operatorname{k}) \mapsto \operatorname{val}((\operatorname{Finset.orderIsoOfFin} (\operatorname{ForestCovers.IntervalForest.support} \operatorname{P}) \operatorname{h} \operatorname{i})) \in \operatorname{ForestCovers.IntervalForest.support} \operatorname{Q})$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.idealCodeOrderIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The isomorphism sends a subforest to the occupied child indices in the increasing enumeration of the host support. Closed subsets preserve the interval-component condition.

**Theorem 1.8 (pi_one_card).**

$$\operatorname{Nat.card} (\operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} 1)) = 3$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IdealCompression.pi_one_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.9 (pi_two_card).**

$$\operatorname{Nat.card} (\operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} 2)) = 6$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IdealCompression.pi_two_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Definition 1.10 (SmallIdealCodes / t1).**

$$\forall (\operatorname{i} : \operatorname{Fin} 1) , \operatorname{SmallIdealCodes.t1} \operatorname{i} = 0$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.t1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is fun _ => 0.

**Definition 1.11 (SmallIdealCodes / t20).**

$$\forall (\operatorname{i} : \operatorname{Fin} 2) , \operatorname{SmallIdealCodes.t20} \operatorname{i} = 0$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.t20` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The defining expression is fun _ => 0.

**Definition 1.12 (SmallIdealCodes / t21).**

$$\forall (\operatorname{i} : \operatorname{Fin} 2) , \operatorname{val}((\operatorname{SmallIdealCodes.t21} \operatorname{i})) = \operatorname{val}(\operatorname{i})$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.t21` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

t21 is the dependent identity code: val(t21 i) = val(i).

**Definition 1.13 (SmallIdealCodes / t3).**

$$\forall (\operatorname{a} : \operatorname{Fin} 2) (\operatorname{b} : \operatorname{Fin} 3) (\operatorname{i} : \operatorname{Fin} 3) , \operatorname{val}((\operatorname{SmallIdealCodes.t3} \operatorname{a} \operatorname{b} \operatorname{i})) = (\operatorname{if} \operatorname{val}(\operatorname{i}) = 0 \operatorname{then} 0 \operatorname{else} \operatorname{if} \operatorname{val}(\operatorname{i}) = 1 \operatorname{then} \operatorname{val}(\operatorname{a}) \operatorname{else} \operatorname{val}(\operatorname{b}))$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.t3` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

t3 has value 0 at index 0, value val(a) at index 1, and value val(b) at index 2.

**Theorem 1.14 (SmallIdealCodes / code_one).**

$$\forall (\operatorname{t} : (\operatorname{v} : \operatorname{Fin} 1) \to \operatorname{Fin} (\operatorname{val}(\operatorname{v}) + 1)) , \operatorname{t} = \operatorname{IdealCompression.SmallIdealCodes.t1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IdealCompression.code_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.15 (SmallIdealCodes / code_two).**

$$\forall (\operatorname{t} : (\operatorname{v} : \operatorname{Fin} 2) \to \operatorname{Fin} (\operatorname{val}(\operatorname{v}) + 1)) , \operatorname{t} = \operatorname{IdealCompression.SmallIdealCodes.t20} \lor \operatorname{t} = \operatorname{IdealCompression.SmallIdealCodes.t21}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IdealCompression.code_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.16 (SmallIdealCodes / code_three).**

$$\forall (\operatorname{t} : (\operatorname{v} : \operatorname{Fin} 3) \to \operatorname{Fin} (\operatorname{val}(\operatorname{v}) + 1)) , \exists (\operatorname{a} : \operatorname{Fin} 2) (\operatorname{b} : \operatorname{Fin} 3) , \operatorname{t} = \operatorname{IdealCompression.SmallIdealCodes.t3} \operatorname{a} \operatorname{b}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IdealCompression.code_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.17 (SmallIdealCodes / card_two_iff).**

$$\forall (\operatorname{t} : (\operatorname{v} : \operatorname{Fin} 2) \to \operatorname{Fin} (\operatorname{val}(\operatorname{v}) + 1)) , \operatorname{Nat.card} \{\operatorname{s} : \operatorname{Finset} (\operatorname{Fin} 2) \mid \operatorname{IdealCompression.CodeClosed} \operatorname{t} \operatorname{s}\} = 3 \iff \operatorname{t} = \operatorname{IdealCompression.SmallIdealCodes.t20}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IdealCompression.card_two_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.18 (SmallIdealCodes / card_three_iff).**

$$\forall (\operatorname{t} : (\operatorname{v} : \operatorname{Fin} 3) \to \operatorname{Fin} (\operatorname{val}(\operatorname{v}) + 1)) , \operatorname{Nat.card} \{\operatorname{s} : \operatorname{Finset} (\operatorname{Fin} 3) \mid \operatorname{IdealCompression.CodeClosed} \operatorname{t} \operatorname{s}\} = 6 \iff \operatorname{t} = \operatorname{IdealCompression.SmallIdealCodes.t3} 0 2 \lor \operatorname{t} = \operatorname{IdealCompression.SmallIdealCodes.t3} 1 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IdealCompression.card_three_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Definition 1.19 (SmallIdealCodes / twoTripleModelsIso).**

$$\forall (\operatorname{s} : \{\operatorname{s} : \operatorname{Finset} (\operatorname{Fin} 3) \mid \operatorname{CodeClosed} (\operatorname{SmallIdealCodes.t3} 0 2) \operatorname{s}\}) , \operatorname{val}((\operatorname{SmallIdealCodes.twoTripleModelsIso} \operatorname{s})) = \operatorname{Finset.image} (\operatorname{fun} (\operatorname{i} : \operatorname{Fin} 3) \mapsto \operatorname{if} \operatorname{i} = 0 \operatorname{then} 1 \operatorname{else} \operatorname{if} \operatorname{i} = 1 \operatorname{then} 2 \operatorname{else} 0) \operatorname{val}(\operatorname{s})$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.twoTripleModelsIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The isomorphism takes the image of each subset under the cycle sending 0 to 1, 1 to 2, and 2 to 0.

**Definition 1.20 (SmallIdealCodes / pi0CodeOrderIso).**

$$\forall (\operatorname{x} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} 0)) , \operatorname{val}((\operatorname{SmallIdealCodes.pi0CodeOrderIso} \operatorname{x})) = \operatorname{Option.elim} (\operatorname{x} : \operatorname{Option} (\operatorname{IntervalForestBasic.IntervalForest} 0)) (\{0\} : \operatorname{Finset} (\operatorname{Fin} 1)) (\operatorname{fun} (\mathord{\cdot} : \operatorname{IntervalForestBasic.IntervalForest} 0) \mapsto (\{\} : \operatorname{Finset} (\operatorname{Fin} 1)))$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.pi0CodeOrderIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The displayed finite map is an order isomorphism from WithTop (IntervalForest 0) to the closed-subset carrier of t1.

**Definition 1.21 (SmallIdealCodes / pi1CodeOrderIso).**

$$\forall (\operatorname{x} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} 1)) , \operatorname{val}((\operatorname{SmallIdealCodes.pi1CodeOrderIso} \operatorname{x})) = \operatorname{Option.elim} (\operatorname{x} : \operatorname{Option} (\operatorname{IntervalForestBasic.IntervalForest} 1)) (\{0 , 1\} : \operatorname{Finset} (\operatorname{Fin} 2)) (\operatorname{fun} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} 1) \mapsto \operatorname{if} \operatorname{P.parent} 1 = \operatorname{none} \operatorname{then} (\{\} : \operatorname{Finset} (\operatorname{Fin} 2)) \operatorname{else} \{0\})$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.pi1CodeOrderIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The displayed finite map is an order isomorphism from WithTop (IntervalForest 1) to the closed-subset carrier of t20.

**Definition 1.22 (SmallIdealCodes / pi2CodeOrderIso).**

$$\forall (\operatorname{x} : \operatorname{WithTop} (\operatorname{IntervalForestBasic.IntervalForest} 2)) , \operatorname{val}((\operatorname{SmallIdealCodes.pi2CodeOrderIso} \operatorname{x})) = \operatorname{Option.elim} (\operatorname{x} : \operatorname{Option} (\operatorname{IntervalForestBasic.IntervalForest} 2)) (\{0 , 1 , 2\} : \operatorname{Finset} (\operatorname{Fin} 3)) (\operatorname{fun} (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} 2) \mapsto \operatorname{if} \operatorname{P.parent} 1 = \operatorname{none} \operatorname{then} (\operatorname{if} \operatorname{P.parent} 2 = \operatorname{none} \operatorname{then} (\{\} : \operatorname{Finset} (\operatorname{Fin} 3)) \operatorname{else} \{2\}) \operatorname{else} (\operatorname{if} \operatorname{P.parent} 2 = \operatorname{none} \operatorname{then} \{0\} \operatorname{else} \operatorname{if} \operatorname{P.parent} 2 = \operatorname{some} 0 \operatorname{then} \{0 , 1\} \operatorname{else} \{0 , 2\}))$$

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/IdealCompression.pi2CodeOrderIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The displayed finite map is an order isomorphism from WithTop (IntervalForest 2) to the closed-subset carrier of t3 0 2.

**Theorem 1.23 (IntervalForest / compressCode_self_iff).**

$$\forall (\operatorname{n} \operatorname{k} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{h} : \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = \operatorname{k}) (\operatorname{i} : \operatorname{Fin} \operatorname{k}) , \operatorname{val}((\operatorname{IdealCompression.IntervalForest.compressCode} \operatorname{P} \operatorname{h} \operatorname{i})) = \operatorname{val}(\operatorname{i}) \iff \operatorname{val}((\operatorname{IdealCompression.IntervalForest.supportParent} \operatorname{P} (\operatorname{Finset.orderIsoOfFin} (\operatorname{ForestCovers.IntervalForest.support} \operatorname{P}) \operatorname{h} \operatorname{i}))) + 1 = \operatorname{val}(\operatorname{val}((\operatorname{Finset.orderIsoOfFin} (\operatorname{ForestCovers.IntervalForest.support} \operatorname{P}) \operatorname{h} \operatorname{i})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IdealCompression.compressCode_self_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

**Theorem 1.24 (IntervalForest / support_adjacent_of_needed).**

$$\forall (\operatorname{n} \operatorname{k} : \operatorname{Nat}) (\operatorname{P} : \operatorname{IntervalForestBasic.IntervalForest} \operatorname{n}) (\operatorname{h} : \operatorname{ForestCovers.IntervalForest.edgeCount} \operatorname{P} = \operatorname{k}) (\operatorname{i} \operatorname{j} : \operatorname{Fin} \operatorname{k}) , \operatorname{val}(\operatorname{i}) + 1 = \operatorname{val}(\operatorname{j}) \to \operatorname{val}((\operatorname{IdealCompression.IntervalForest.compressCode} \operatorname{P} \operatorname{h} \operatorname{j})) \leq \operatorname{val}(\operatorname{i}) \to \operatorname{val}(\operatorname{val}((\operatorname{Finset.orderIsoOfFin} (\operatorname{ForestCovers.IntervalForest.support} \operatorname{P}) \operatorname{h} \operatorname{i}))) + 1 = \operatorname{val}(\operatorname{val}((\operatorname{Finset.orderIsoOfFin} (\operatorname{ForestCovers.IntervalForest.support} \operatorname{P}) \operatorname{h} \operatorname{j})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/IdealCompression.support_adjacent_of_needed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Adrián Lillo and Mercedes Rosas (2026). *The Priority Lattice*. DOI: [10.48550/arXiv.2603.28905](https://doi.org/10.48550/arXiv.2603.28905). URL: <https://arxiv.org/abs/2603.28905v1>.

*Commentary.*

The quantified statement holds for every parameter satisfying its displayed hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.CodeClosed`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.card_three_iff`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.card_two_iff`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.code_one`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.code_three`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.code_two`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.compressCode`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.compressCode_self_iff`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.firstIndex`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.firstNeeded`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.idealCodeOrderIso`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.pi0CodeOrderIso`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.pi1CodeOrderIso`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.pi2CodeOrderIso`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.pi_one_card`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.pi_two_card`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.supportParent`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.supportParent_spec`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.support_adjacent_of_needed`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.t1`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.t20`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.t21`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.t3`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/IdealCompression.twoTripleModelsIso`
- Dependency: [D5/S3/Combinatorics/PriorityLattice/ForestCovers](ForestCovers.md)
