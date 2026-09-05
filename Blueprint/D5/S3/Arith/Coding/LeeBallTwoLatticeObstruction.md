# Radius-Two Lee Ball Lattice Obstruction

## Abstract

The three-dimensional radius-two Lee ball fails to inject into every index-twenty-five lattice quotient.

**Definition 1.1 (The complete radius-two Lee ball).**

$$leeBallTwo = \{(-2, 0, 0), (-1, -1, 0), (-1, 0, -1), (-1, 0, 0), (-1, 0, 1), (-1, 1, 0), (0, -2, 0), (0, -1, -1), (0, -1, 0), (0, -1, 1), (0, 0, -2), (0, 0, -1), (0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 1, -1), (0, 1, 0), (0, 1, 1), (0, 2, 0), (1, -1, 0), (1, 0, -1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (2, 0, 0)\} \subseteq \mathbb{Z}^{3}.$$

*Formalization.* `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.leeBallTwo` (`✓ std3`).

*Citation.* Sylvain Gravier and Michel Mollard and Charles Payan (1998). *On the Non-existence of 3-Dimensional Tiling in the Lee Metric*. DOI: [10.1006/eujc.1998.0211](https://doi.org/10.1006/eujc.1998.0211).

*Commentary.*

The definition lists all twenty-five integer triples in the three-dimensional radius-two Lee ball. The following membership theorem verifies that this finite enumeration is exactly the set cut out by the stated l1 inequality.

**Theorem 1.2 (Enumeration equals the Lee inequality).**

$$\forall x \in \mathbb{Z}^{3}, x \in leeBallTwo \Leftrightarrow \lvert x_{0} \rvert + \lvert x_{1} \rvert + \lvert x_{2} \rvert \leq 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.mem_leeBallTwo_iff` (`✓ std3`). ∎

*Citation.* Sylvain Gravier and Michel Mollard and Charles Payan (1998). *On the Non-existence of 3-Dimensional Tiling in the Lee Metric*. DOI: [10.1006/eujc.1998.0211](https://doi.org/10.1006/eujc.1998.0211).

*Commentary.*

Every listed point has l1 norm at most two, and a bounded integer case split proves that every triple satisfying the inequality occurs in the list.

**Theorem 1.3 (The ball has twenty-five points).**

$$\lvert leeBallTwo \rvert = 25.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.leeBallTwo_card` (`✓ std3`). ∎

*Citation.* Sylvain Gravier and Michel Mollard and Charles Payan (1998). *On the Non-existence of 3-Dimensional Tiling in the Lee Metric*. DOI: [10.1006/eujc.1998.0211](https://doi.org/10.1006/eujc.1998.0211).

*Commentary.*

Kernel reduction checks the cardinality of the complete explicit enumeration; no native evaluator is used.

**Theorem 1.4 (Second moment over ZMod 25).**

$$\forall a: \operatorname{Fin}\left(3\right) \to \operatorname{ZMod}\left(25\right), \sum_{x \in leeBallTwo} (\sum_{i \in \operatorname{Fin}\left(3\right)} a_{i} \cdot [x_{i}]_{25})^{2} = 18 \cdot \sum_{i \in \operatorname{Fin}\left(3\right)} a_{i}^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.leeBallTwo_second_moment` (`✓ std3`). ∎

*Citation.* Sylvain Gravier and Michel Mollard and Charles Payan (1998). *On the Non-existence of 3-Dimensional Tiling in the Lee Metric*. DOI: [10.1006/eujc.1998.0211](https://doi.org/10.1006/eujc.1998.0211).

*Commentary.*

For each coefficient vector, every integer coordinate is reduced modulo twenty-five before multiplication. Expansion of the twenty-five terms gives eighteen times the coordinate-square sum.

**Theorem 1.5 (Fourth moment over ZMod 25).**

$$\forall a: \operatorname{Fin}\left(3\right) \to \operatorname{ZMod}\left(25\right), \sum_{x \in leeBallTwo} (\sum_{i \in \operatorname{Fin}\left(3\right)} a_{i} \cdot [x_{i}]_{25})^{4} = 30 \cdot \sum_{i \in \operatorname{Fin}\left(3\right)} a_{i}^{4} + 12 \cdot (\sum_{i \in \operatorname{Fin}\left(3\right)} a_{i}^{2})^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.leeBallTwo_fourth_moment` (`✓ std3`). ∎

*Citation.* Sylvain Gravier and Michel Mollard and Charles Payan (1998). *On the Non-existence of 3-Dimensional Tiling in the Lee Metric*. DOI: [10.1006/eujc.1998.0211](https://doi.org/10.1006/eujc.1998.0211).

*Commentary.*

The fourth-power expansion separates into thirty times the fourth power sum and twelve times the square of the second power sum. All operations occur in ZMod 25.

**Theorem 1.6 (The cyclic readout is never injective).**

$$\forall a: \operatorname{Fin}\left(3\right) \to \operatorname{ZMod}\left(25\right), \neg \operatorname{InjOn}\left((x \mapsto \sum_{i \in \operatorname{Fin}\left(3\right)} a_{i} \cdot [x_{i}]_{25}), leeBallTwo\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.zmod25_readout_not_injective` (`✓ std3`). ∎

*Citation.* Sylvain Gravier and Michel Mollard and Charles Payan (1998). *On the Non-existence of 3-Dimensional Tiling in the Lee Metric*. DOI: [10.1006/eujc.1998.0211](https://doi.org/10.1006/eujc.1998.0211).

*Commentary.*

Injectivity would identify the ball with all residues modulo twenty-five. The complete second and fourth residue moments then force a fourth-power sum congruent to four modulo five, while three fourth powers over F5 can sum only to zero, one, two, or three.

**Theorem 1.7 (The elementary readout is never injective).**

$$\forall a, b: \operatorname{Fin}\left(3\right) \to \operatorname{ZMod}\left(5\right), \neg \operatorname{InjOn}\left((x \mapsto (\sum_{i \in \operatorname{Fin}\left(3\right)} a_{i} \cdot [x_{i}]_{5}, \sum_{i \in \operatorname{Fin}\left(3\right)} b_{i} \cdot [x_{i}]_{5})), leeBallTwo\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.zmod5_pair_readout_not_injective` (`✓ std3`). ∎

*Citation.* Sylvain Gravier and Michel Mollard and Charles Payan (1998). *On the Non-existence of 3-Dimensional Tiling in the Lee Metric*. DOI: [10.1006/eujc.1998.0211](https://doi.org/10.1006/eujc.1998.0211).

*Commentary.*

Every nonzero linear functional on F5 squared has five points in each fibre. Fibrewise summation and the second moment make the span of the two coefficient vectors totally isotropic. The explicit ternary F5 calculation then makes the vectors dependent, contradicting an injective paired readout.

**Theorem 1.8 (Classification of additive groups of order twenty-five).**

$$\forall G: Type, [\operatorname{AddCommGroup}\left(G\right)], \lvert G \rvert = 25 \Rightarrow (\operatorname{Nonempty}\left(G \sim_{+} \operatorname{ZMod}\left(25\right)\right) \lor \operatorname{Nonempty}\left(G \sim_{+} \operatorname{ZMod}\left(5\right) \times \operatorname{ZMod}\left(5\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.addCommGroup_card_twenty_five_classification` (`✓ std3`). ∎

*Citation.* Sylvain Gravier and Michel Mollard and Charles Payan (1998). *On the Non-existence of 3-Dimensional Tiling in the Lee Metric*. DOI: [10.1006/eujc.1998.0211](https://doi.org/10.1006/eujc.1998.0211).

*Commentary.*

The cyclic case is equivalent to ZMod 25. In the noncyclic case, exponent five supplies a ZMod 5 module; its cardinality forces finrank two and hence an additive equivalence with F5 squared.

**Theorem 1.9 (No index-twenty-five lattice quotient separates the ball).**

$$\forall L: \operatorname{AddSubgroup}\left(\mathbb{Z}^{3}\right), \lvert \mathbb{Z}^{3}/L \rvert = 25 \Rightarrow \neg \operatorname{InjOn}\left((x \mapsto [x]_{L}), leeBallTwo\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.leeBallTwo_lattice_obstruction` (`✓ std3`). ∎

*Citation.* Sylvain Gravier and Michel Mollard and Charles Payan (1998). *On the Non-existence of 3-Dimensional Tiling in the Lee Metric*. DOI: [10.1006/eujc.1998.0211](https://doi.org/10.1006/eujc.1998.0211).

*Commentary.*

The quotient has order twenty-five, so the classification sends it to either the cyclic or elementary readout obstruction. Thus two points of the radius-two Lee ball have the same quotient class.

This module is an independent kernel-checked proof of the n = 3 lattice case proved by Gravier, Mollard, and Payan in 1998. Leung and Zhou proved the radius-two lattice result for every n at least three in 2020 (arXiv:1808.08520). The formal theorem asserts nothing about non-lattice tilings, other dimensions, or other radii; the cited papers are provenance rather than Lean proof dependencies.

## References

- Truth anchor: `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.addCommGroup_card_twenty_five_classification`
- Truth anchor: `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.leeBallTwo`
- Truth anchor: `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.leeBallTwo_card`
- Truth anchor: `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.leeBallTwo_fourth_moment`
- Truth anchor: `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.leeBallTwo_lattice_obstruction`
- Truth anchor: `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.leeBallTwo_second_moment`
- Truth anchor: `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.mem_leeBallTwo_iff`
- Truth anchor: `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.zmod25_readout_not_injective`
- Truth anchor: `D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction.zmod5_pair_readout_not_injective`
