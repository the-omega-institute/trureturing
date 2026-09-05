# Erdos--Straus Modular Witnesses

## Abstract

Five modular families have explicit positive Erdos--Straus witnesses.

**Theorem 1.1 (Five congruence families admit explicit reciprocal decompositions).**

$$\begin{aligned}(\forall q: \mathbb{N}, 0 < q \Rightarrow \operatorname{IsErdosStrausWitness}(2 \times q, q, 2 \times q, 2 \times q)) \land\\{}(\forall q: \mathbb{N}, 0 < q \Rightarrow \operatorname{IsErdosStrausWitness}(3 \times q, q, 4 \times q, 12 \times q)) \land\\{}(\forall k: \mathbb{N}, \operatorname{IsErdosStrausWitness}(3 \times k + 2, k + 1, 3 \times k + 2, (3 \times k + 2) \times (k + 1))) \land\\{}(\forall k: \mathbb{N}, \operatorname{IsErdosStrausWitness}(4 \times k + 3, k + 1, 2 \times (4 \times k + 3) \times (k + 1), 2 \times (4 \times k + 3) \times (k + 1))) \land\\{}(\forall k: \mathbb{N}, \operatorname{IsErdosStrausWitness}(8 \times k + 5, 2 \times k + 2, (8 \times k + 5) \times (k + 1), 2 \times (8 \times k + 5) \times (k + 1))) \land\\{}\operatorname{IsErdosStrausWitness}(2, 1, 2, 2) \land\\{}\operatorname{IsErdosStrausWitness}(5, 2, 5, 10) \land\\{}\operatorname{IsErdosStrausWitness}(7, 2, 28, 28).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ErdosStrausModularWitnesses.erdos_straus_modular_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write a positive even integer as 2q and a positive multiple of three as 3q. Their displayed denominator triples are positive and solve four over n as a sum of three unit fractions.

For arbitrary k, the constructions also solve the classes 3k+2, 4k+3, and 8k+5. Positivity is part of the witness predicate, so none of the rational divisions uses a zero denominator.

The three final clauses verify the concrete triples (1,2,2), (2,5,10), and (2,28,28) for n equal to 2, 5, and 7.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ErdosStrausModularWitnesses.erdos_straus_modular_witnesses`
