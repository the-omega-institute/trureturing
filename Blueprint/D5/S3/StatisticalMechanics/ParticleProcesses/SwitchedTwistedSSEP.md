# Switched twisted symmetric exclusion processes

## Abstract

Alternating equilibrated twisted exclusion models have full support exactly under the derived-group or two-site pair-group criterion.

The source is Dabrowski, Poulain d’Andecy and Ragoucy, Sections 3.1, 4, 5.1 and 7. Sites use zero-based Fin L indices; species use Fin N. The source assumes N positive and L at least two. The formal statement also covers N zero, where configurations form an empty space. The evolution is the equilibrated switching of Proposition 5.2: each model is run to its sector-uniform stationary distribution. No finite-time relaxation rate is asserted.

**Definition 1.1 (Configuration).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right) = \left(\left(\operatorname{Fin}\left(\operatorname{L}\right)\right) \to \left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.Configuration` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

A configuration assigns one species to each lattice site.

**Definition 1.2 (adjacentMove).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{i}: \operatorname{Fin}\left(\operatorname{L}\right)\right), \left(\forall \left(\operatorname{hi}: \operatorname{Fin.val}\left(\operatorname{i}\right) + 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\operatorname{adjacentMove}\left(\operatorname{i}, \operatorname{hi}, \operatorname{x}\right) = \operatorname{Function.comp}\left(\operatorname{x}, \operatorname{Equiv.swap}\left(\operatorname{i}, \left(\operatorname{Fin.val}\left(\operatorname{i}\right) + 1: \operatorname{Fin}\left(\operatorname{L}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.adjacentMove` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

Exchange sites i and i plus one, with the explicit upper-bound proof hi.

**Definition 1.3 (lastSite).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\left(\operatorname{lastSite}\left(\operatorname{hL}\right): \operatorname{Fin}\left(\operatorname{L}\right)\right) = \left(\operatorname{L} - 1: \operatorname{Fin}\left(\operatorname{L}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.lastSite` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

The final site has natural value L minus one; hL supplies its bound.

**Definition 1.4 (firstSite).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\left(\operatorname{firstSite}\left(\operatorname{hL}\right): \operatorname{Fin}\left(\operatorname{L}\right)\right) = \left(0: \operatorname{Fin}\left(\operatorname{L}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.firstSite` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

The first site has natural value zero.

**Definition 1.5 (boundaryMove).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{s}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\forall \left(\operatorname{i}: \operatorname{Fin}\left(\operatorname{L}\right)\right), \left(\operatorname{boundaryMove}\left(\operatorname{hL}, \operatorname{s}, \operatorname{x}\right)\left(\operatorname{i}\right) = \operatorname{ite}\left(\operatorname{i} = \operatorname{firstSite}\left(\operatorname{hL}\right), \left(\left(\operatorname{s}\right)^{-1}\right)\left(\operatorname{x}\left(\operatorname{lastSite}\left(\operatorname{hL}\right)\right)\right), \operatorname{ite}\left(\operatorname{i} = \operatorname{lastSite}\left(\operatorname{hL}\right), \operatorname{s}\left(\operatorname{x}\left(\operatorname{firstSite}\left(\operatorname{hL}\right)\right)\right), \operatorname{x}\left(\operatorname{i}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.boundaryMove` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

At the first site take the inverse twist of the last entry; at the last site take the twist of the first entry. Other sites retain their entries. This is equation 3.3.

**Definition 1.6 (moveRelation).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{s}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\forall \left(\operatorname{y}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\left(\operatorname{moveRelation}\left(\operatorname{hL}, \operatorname{s}, \operatorname{x}, \operatorname{y}\right)\right) \Leftrightarrow \left(\left(\exists \left(\operatorname{i}: \operatorname{Fin}\left(\operatorname{L}\right)\right), \left(\exists \left(\operatorname{hi}: \operatorname{Fin.val}\left(\operatorname{i}\right) + 1 < \operatorname{L}\right), \left(\operatorname{y} = \operatorname{adjacentMove}\left(\operatorname{i}, \operatorname{hi}, \operatorname{x}\right)\right)\right)\right) \lor \left(\operatorname{y} = \operatorname{boundaryMove}\left(\operatorname{hL}, \operatorname{s}, \operatorname{x}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.moveRelation` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

An elementary move is either one allowed adjacent exchange or the twisted boundary exchange. Every elementary move is an involution.

**Definition 1.7 (sector).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{s}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\operatorname{sector}\left(\operatorname{hL}, \operatorname{s}, \operatorname{x}\right) = \operatorname{Finset.filter}\left(\lambda \left(\operatorname{y}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right) \mapsto \left(\operatorname{Relation.EqvGen}\left(\operatorname{moveRelation}\left(\operatorname{hL}, \operatorname{s}\right), \operatorname{x}, \operatorname{y}\right)\right), \left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.sector` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

A sector is the finite set of configurations in the equivalence closure of the elementary moves. It contains its representative.

**Definition 1.8 (branchingProbability).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{s}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{t}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\forall \left(\operatorname{y}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\left(\operatorname{branchingProbability}\left(\operatorname{hL}, \operatorname{s}, \operatorname{t}, \operatorname{x}, \operatorname{y}\right): \mathbb{Q}\right) = \frac{\left(\operatorname{Finset.card}\left(\operatorname{inf}\left(\operatorname{sector}\left(\operatorname{hL}, \operatorname{s}, \operatorname{x}\right), \operatorname{sector}\left(\operatorname{hL}, \operatorname{t}, \operatorname{y}\right)\right)\right): \mathbb{Q}\right)}{\left(\operatorname{Finset.card}\left(\operatorname{sector}\left(\operatorname{hL}, \operatorname{s}, \operatorname{x}\right)\right): \mathbb{Q}\right)}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.branchingProbability` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

Proposition 5.2 assigns the intersection cardinality divided by the initial sector cardinality. The denominator is strictly positive because the initial representative belongs to its sector.

**Definition 1.9 (overlap).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{s}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{t}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\forall \left(\operatorname{y}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\left(\operatorname{overlap}\left(\operatorname{hL}, \operatorname{s}, \operatorname{t}, \operatorname{x}, \operatorname{y}\right)\right) \Leftrightarrow \left(\operatorname{Finset.Nonempty}\left(\operatorname{inf}\left(\operatorname{sector}\left(\operatorname{hL}, \operatorname{s}, \operatorname{x}\right), \operatorname{sector}\left(\operatorname{hL}, \operatorname{t}, \operatorname{y}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.overlap` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

The two sectors overlap exactly when their intersection contains a configuration.

**Definition 1.10 (unionMoveRelation).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\forall \left(\operatorname{y}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\left(\operatorname{unionMoveRelation}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{x}, \operatorname{y}\right)\right) \Leftrightarrow \left(\left(\operatorname{moveRelation}\left(\operatorname{hL}, \operatorname{f}, \operatorname{x}, \operatorname{y}\right)\right) \lor \left(\operatorname{moveRelation}\left(\operatorname{hL}, \operatorname{g}, \operatorname{x}, \operatorname{y}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.unionMoveRelation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

The union graph allows an elementary move of either twist.

**Definition 1.11 (unionConnected).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\left(\operatorname{unionConnected}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}\right)\right) \Leftrightarrow \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\forall \left(\operatorname{y}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\operatorname{Relation.EqvGen}\left(\operatorname{unionMoveRelation}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}\right), \operatorname{x}, \operatorname{y}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.unionConnected` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

Connected means that every ordered pair of configurations belongs to the union relation's equivalence closure.

**Definition 1.12 (sectorsOf).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{s}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{C}: \operatorname{Finset}\left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right)\right), \left(\left(\operatorname{C} \in \operatorname{sectorsOf}\left(\operatorname{hL}, \operatorname{s}\right)\right) \Leftrightarrow \left(\exists \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\operatorname{C} = \operatorname{sector}\left(\operatorname{hL}, \operatorname{s}, \operatorname{x}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.sectorsOf` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

The sector family consists exactly of sectors obtained from a representative configuration.

**Definition 1.13 (alternatingSectorReach).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{start}: \operatorname{Bool}\right), \left(\forall \left(\operatorname{C}: \operatorname{Finset}\left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right)\right), \left(\left(\forall \left(\operatorname{D}: \operatorname{Finset}\left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right)\right), \left(\left(\operatorname{D} \in \operatorname{alternatingSectorReach}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{start}, \operatorname{C}, 0\right)\right) \Leftrightarrow \left(\operatorname{D} = \operatorname{C}\right)\right)\right) \land \left(\forall \left(\operatorname{k}: \mathbb{N}\right), \left(\forall \left(\operatorname{D}: \operatorname{Finset}\left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right)\right), \left(\left(\operatorname{D} \in \operatorname{alternatingSectorReach}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{start}, \operatorname{C}, \operatorname{k} + 1\right)\right) \Leftrightarrow \left(\left(\operatorname{D} \in \operatorname{sectorsOf}\left(\operatorname{hL}, \operatorname{ite}\left(\operatorname{start} = \operatorname{BEq.beq}\left(\operatorname{Nat.mod}\left(\operatorname{k}, 2\right), 0\right), \operatorname{g}, \operatorname{f}\right)\right)\right) \land \left(\exists \left(\operatorname{E}: \operatorname{Finset}\left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right)\right), \left(\left(\operatorname{E} \in \operatorname{alternatingSectorReach}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{start}, \operatorname{C}, \operatorname{k}\right)\right) \land \left(\operatorname{Finset.Nonempty}\left(\operatorname{inf}\left(\operatorname{E}, \operatorname{D}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.alternatingSectorReach` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

At zero steps the reached sector set is the singleton initial set C. At step k plus one use g when start equals the Boolean test that k is even, and f otherwise. Keep precisely sectors intersecting a previously reached set. This formula also defines the operation for arbitrary finite initial C.

**Definition 1.14 (switchSupport).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{start}: \operatorname{Bool}\right), \left(\forall \left(\operatorname{C}: \operatorname{Finset}\left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{k}: \mathbb{N}\right), \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\left(\operatorname{x} \in \operatorname{switchSupport}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{start}, \operatorname{C}, \operatorname{k}\right)\right) \Leftrightarrow \left(\exists \left(\operatorname{D}: \operatorname{Finset}\left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right)\right), \left(\left(\operatorname{D} \in \operatorname{alternatingSectorReach}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{start}, \operatorname{C}, \operatorname{k}\right)\right) \land \left(\operatorname{x} \in \operatorname{D}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.switchSupport` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

The support is the union of the sectors reached after k steps.

**Definition 1.15 (alternatingSupport).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{start}: \operatorname{Bool}\right), \left(\forall \left(\operatorname{C}: \operatorname{Finset}\left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right)\right), \left(\left(\operatorname{alternatingSupport}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{start}, \operatorname{C}, 0\right) = \operatorname{Finset.coe}\left(\operatorname{C}\right)\right) \land \left(\forall \left(\operatorname{k}: \mathbb{N}\right), \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\left(\operatorname{x} \in \operatorname{alternatingSupport}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{start}, \operatorname{C}, \operatorname{k} + 1\right)\right) \Leftrightarrow \left(\exists \left(\operatorname{D}: \operatorname{Finset}\left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right)\right), \left(\left(\operatorname{D} \in \operatorname{sectorsOf}\left(\operatorname{hL}, \operatorname{ite}\left(\operatorname{start} = \operatorname{BEq.beq}\left(\operatorname{Nat.mod}\left(\operatorname{k}, 2\right), 0\right), \operatorname{g}, \operatorname{f}\right)\right)\right) \land \left(\left(\operatorname{x} \in \operatorname{D}\right) \land \left(\exists \left(\operatorname{y}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\left(\operatorname{y} \in \operatorname{alternatingSupport}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{start}, \operatorname{C}, \operatorname{k}\right)\right) \land \left(\operatorname{y} \in \operatorname{D}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.alternatingSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

The recursive configuration support begins with C and at each step includes every configuration in a next-model sector containing a configuration of the preceding support.

**Definition 1.16 (twistGroup).**

$$\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\operatorname{twistGroup}\left(\operatorname{f}, \operatorname{g}\right) = \operatorname{Subgroup.closure}\left(\left\{\operatorname{f}, \operatorname{g}\right\}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.twistGroup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

H is the subgroup of species permutations generated by f and g.

**Definition 1.17 (derivedTwistGroup).**

$$\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\operatorname{derivedTwistGroup}\left(\operatorname{f}, \operatorname{g}\right) = \operatorname{Subgroup.map}\left(\operatorname{Subgroup.subtype}\left(\operatorname{twistGroup}\left(\operatorname{f}, \operatorname{g}\right)\right), \operatorname{commutator}\left(\operatorname{twistGroup}\left(\operatorname{f}, \operatorname{g}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.derivedTwistGroup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

The derived group is the image in the ambient permutation group of the commutator subgroup of H. This is precisely the subgroup commutator of H with itself.

**Definition 1.18 (pairTwistGroup).**

$$\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\operatorname{pairTwistGroup}\left(\operatorname{f}, \operatorname{g}\right) = \operatorname{Subgroup.closure}\left(\left\{\left(\operatorname{f}, \left(\operatorname{f}\right)^{-1}\right), \left(\operatorname{g}, \left(\operatorname{g}\right)^{-1}\right)\right\}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.pairTwistGroup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

K is generated by the two pairs consisting of a twist and its inverse.

**Definition 1.19 (pointStabilizer).**

$$\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{H}: \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right)\right), \left(\forall \left(\operatorname{a}: \operatorname{Fin}\left(\operatorname{N}\right)\right), \left(\operatorname{pointStabilizer}\left(\operatorname{H}, \operatorname{a}\right) = \operatorname{inf}\left(\operatorname{H}, \operatorname{MulAction.stabilizer}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right), \operatorname{a}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.pointStabilizer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

Intersect H with the ambient stabilizer of the species a.

**Definition 1.20 (pointPairStabilizer).**

$$\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{H}: \operatorname{Subgroup}\left(\operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right)\right), \left(\forall \left(\operatorname{a}: \operatorname{Fin}\left(\operatorname{N}\right)\right), \left(\operatorname{pointPairStabilizer}\left(\operatorname{H}, \operatorname{a}\right) = \operatorname{Subgroup.prod}\left(\operatorname{pointStabilizer}\left(\operatorname{H}, \operatorname{a}\right), \operatorname{pointStabilizer}\left(\operatorname{H}, \operatorname{a}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.pointPairStabilizer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

Take the direct product of the two point stabilizers.

**Definition 1.21 (lTwoCriterion).**

$$\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\left(\operatorname{lTwoCriterion}\left(\operatorname{f}, \operatorname{g}\right)\right) \Leftrightarrow \left(\forall \left(\operatorname{a}: \operatorname{Fin}\left(\operatorname{N}\right)\right), \left(\operatorname{Nat.card}\left(\operatorname{pairTwistGroup}\left(\operatorname{f}, \operatorname{g}\right)\right) = \operatorname{N}^{2} \cdot \operatorname{Nat.card}\left(\operatorname{inf}\left(\operatorname{pairTwistGroup}\left(\operatorname{f}, \operatorname{g}\right), \operatorname{pointPairStabilizer}\left(\operatorname{twistGroup}\left(\operatorname{f}, \operatorname{g}\right), \operatorname{a}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.lTwoCriterion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

For every a, the cardinality of K equals N squared times the cardinality of its intersection with the product stabilizer. The proof identifies this intersection with the stabilizer of the diagonal pair in K. Orbit-stabilizer then gives a full orbit.

**Definition 1.22 (lAtLeastThreeCriterion).**

$$\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\left(\operatorname{lAtLeastThreeCriterion}\left(\operatorname{f}, \operatorname{g}\right)\right) \Leftrightarrow \left(\operatorname{MulAction.IsPretransitive}\left(\operatorname{derivedTwistGroup}\left(\operatorname{f}, \operatorname{g}\right), \operatorname{Fin}\left(\operatorname{N}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.lAtLeastThreeCriterion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

For at least three sites the commutator subgroup must act transitively on the species.

**Definition 1.23 (fullSwitchingReachability).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\left(\operatorname{fullSwitchingReachability}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}\right)\right) \Leftrightarrow \left(\forall \left(\operatorname{start}: \operatorname{Bool}\right), \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\forall \left(\operatorname{target}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\exists \left(\operatorname{k}: \mathbb{N}\right), \left(\operatorname{target} \in \operatorname{switchSupport}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{start}, \operatorname{sector}\left(\operatorname{hL}, \operatorname{ite}\left(\operatorname{start}, \operatorname{f}, \operatorname{g}\right), \operatorname{x}\right), \operatorname{k}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.fullSwitchingReachability` (`✓ std3`).

*Citation.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

From every representative of a sector of either model, every target belongs to the support after some finite number k of alternating sector steps. Start true denotes the f-sector and start false the g-sector.

**Definition 1.24 (registeredReachabilityAnswer).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\left(\operatorname{registeredReachabilityAnswer}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}\right)\right) \Leftrightarrow \left(\left(\operatorname{fullSwitchingReachability}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}\right)\right) \Leftrightarrow \left(\left(\operatorname{unionConnected}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}\right)\right) \land \left(\operatorname{ite}\left(3 \le \operatorname{L}, \operatorname{lAtLeastThreeCriterion}\left(\operatorname{f}, \operatorname{g}\right), \operatorname{lTwoCriterion}\left(\operatorname{f}, \operatorname{g}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.registeredReachabilityAnswer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

The full support property is equivalent to union connectivity together with the appropriate criterion. Since hL asserts L greater than one, the alternative to L at least three is exactly L equal to two.

**Theorem 1.25 (The complete reachability classification).**

$$\forall \left(\operatorname{L}: \mathbb{N}\right), \left(\forall \left(\operatorname{N}: \mathbb{N}\right), \left(\forall \left(\operatorname{hL}: 1 < \operatorname{L}\right), \left(\forall \left(\operatorname{f}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{g}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\left(\operatorname{registeredReachabilityAnswer}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}\right)\right) \land \left(\left(\left(\left(3 \le \operatorname{L}\right) \Rightarrow \left(\left(\operatorname{unionConnected}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}\right)\right) \Leftrightarrow \left(\operatorname{lAtLeastThreeCriterion}\left(\operatorname{f}, \operatorname{g}\right)\right)\right)\right) \land \left(\left(\operatorname{L} = 2\right) \Rightarrow \left(\left(\operatorname{unionConnected}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}\right)\right) \Leftrightarrow \left(\operatorname{lTwoCriterion}\left(\operatorname{f}, \operatorname{g}\right)\right)\right)\right)\right) \land \left(\left(\forall \left(\operatorname{s}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{t}: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(\operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{x}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\forall \left(\operatorname{y}: \operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right), \left(\left(\operatorname{overlap}\left(\operatorname{hL}, \operatorname{s}, \operatorname{t}, \operatorname{x}, \operatorname{y}\right)\right) \Leftrightarrow \left(\left(0: \mathbb{Q}\right) < \operatorname{branchingProbability}\left(\operatorname{hL}, \operatorname{s}, \operatorname{t}, \operatorname{x}, \operatorname{y}\right)\right)\right)\right)\right)\right)\right) \land \left(\forall \left(\operatorname{start}: \operatorname{Bool}\right), \left(\forall \left(\operatorname{C}: \operatorname{Finset}\left(\operatorname{Configuration}\left(\operatorname{L}, \operatorname{N}\right)\right)\right), \left(\forall \left(\operatorname{k}: \mathbb{N}\right), \left(\operatorname{alternatingSupport}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{start}, \operatorname{C}, \operatorname{k}\right) = \operatorname{switchSupport}\left(\operatorname{hL}, \operatorname{f}, \operatorname{g}, \operatorname{start}, \operatorname{C}, \operatorname{k}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.result` (`✓ std3`). ∎

*Resolves.* `Problems/dabrowski-poulain-ragoucy-2026-switched-ssep-reachability` (proved) by `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dabrowski-poulain-ragoucy-2026-switched-ssep-reachability","declaration_gid":"D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mathieu Dabrowski; Loïc Poulain d’Andecy; Eric Ragoucy (2026). *Twisted symmetric exclusion processes and set-theoretical R-matrices*. DOI: [10.1088/1751-8121/ae751a](https://doi.org/10.1088/1751-8121/ae751a). URL: <https://arxiv.org/html/2602.18204v2>.

*Commentary.*

All natural N, all L greater than one, and every pair f,g are quantified. The first conjunct is the full registered answer. The second gives both directions between union connectivity and the group criterion. The third states Proposition 5.2 positivity exactly. The fourth identifies recursive configuration support with alternating sector closure for every finite initial set and every step count.

For switching, each union move is absorbed by at most two alternating sector expansions, and these supports grow with the step count. Every expansion stays inside the starting union component. These two statements give the connectivity equivalence.

Adjacent transpositions generate every site permutation. Composing the boundary exchange with the endpoint transposition yields a paired twist operation, and conjugating by site permutations places it at any distinct pair. The projection of K onto its first factor contains H. Lift arbitrary h and k in H onto the coordinate pairs i,j and i,k. Their commutator acts only at i. Subgroup.commutator_le gives every derived-group operation at each coordinate independently, which proves sufficiency when three sites are available.

The coordinate homomorphisms are assembled with MonoidHom.pi and MonoidHom.mulSingle. A paired coordinate operation updates a Pi.mulSingle function at the other coordinate. The pair action is Prod.mulAction applied to the actions pulled back along the two projections by MulAction.compHom. Equiv.Perm.exists_extending_pair supplies the site permutation, and Fin.exists_ne_and_ne_of_two_lt supplies distinct auxiliary sites. Site and coordinate reachability subgroups are stabilizers of the union-component quotient map under arrowAction; Subgroup.copy retains their path predicates. Relation.EqvGen.eqvGen_le extends an elementary-move invariant to the whole union component.

For necessity, connectivity first forces H to be transitive, since all entries of a configuration remain within the H-orbit of a constant initial species. Fix a species a and form the normal subgroup P given by the join of the commutator of H with the stabilizer of a. The quotient H/P is abelian. The charge of h acting on a is the quotient class of h; the stabilizer inclusion makes this well defined. Its product over all sites is invariant under exchanges and the paired twist. Connectivity to a configuration changing just one entry forces every charge to be the identity. Writing an element of P as a derived element times a stabilizer element proves derived-group transitivity.

For two sites the flip sends each paired generator to its inverse, hence normalizes K and fixes every diagonal pair. The union component of a diagonal configuration is exactly its K-orbit. The two-site criterion follows from orbit-stabilizer and the existing Mathlib pretransitivity characterization. The stabilizer identification uses MulEquiv.subgroupCongr and Subgroup.subgroupOfEquivOfLe after identifying the subgroup predicates. The argument is uniform in the number of sites, the number of species and the two permutations.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.Configuration`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.adjacentMove`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.alternatingSectorReach`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.alternatingSupport`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.boundaryMove`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.branchingProbability`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.derivedTwistGroup`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.firstSite`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.fullSwitchingReachability`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.lAtLeastThreeCriterion`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.lTwoCriterion`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.lastSite`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.moveRelation`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.overlap`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.pairTwistGroup`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.pointPairStabilizer`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.pointStabilizer`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.registeredReachabilityAnswer`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.result`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.sector`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.sectorsOf`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.switchSupport`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.twistGroup`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.unionConnected`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/SwitchedTwistedSSEP.unionMoveRelation`
