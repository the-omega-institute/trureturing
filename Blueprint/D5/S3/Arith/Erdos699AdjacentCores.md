# Erdos 699 Adjacent-Core Bound

## Abstract

Adjacent coprime divisibility cores obey a cubic necessary bound.

**Theorem 1.1 (Cubic bound from adjacent cores).**

$$\forall n \in \mathbb{N}, M \in \mathbb{N}, t \in \mathbb{N}, R1 \in \mathbb{N}, R2 \in \mathbb{N}, delta1 \in \mathbb{N}, delta2 \in \mathbb{N},\; \left(\left(\left(\left(\left(\left(\left(\left(0 < t \land 2 \cdot t < M\right) \land Coprime(R1, R2)\right) \land R1 \mid t \cdot \left(M - t\right)\right) \land R2 \mid t \cdot \left(M - t\right) \cdot \left(M - 2 \cdot t\right)\right) \land delta1 \le 3\right) \land delta2 \le 3\right) \land n = delta1 \cdot R1 + 1\right) \land n = 2 \cdot delta2 \cdot R2 + 2\right) \Rightarrow \left(\left(n - 1\right) \cdot \left(n - 2\right)\right)^{2} \le 3 \cdot M^{6}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Erdos699AdjacentCores.adjacent_core_numerator_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All variables range over natural numbers, and subtraction is truncated natural subtraction. The assumptions are precisely the displayed positivity, half-range, coprimality, divisibility, defect bounds and two equations for n. No binomial coefficient or Lucas condition is asserted by this theorem.

Coprimality makes the product of the two cores divide t(M-t)(M-2t). The identity 4(M^6-108[t(M-t)(M-2t)]^2)=(M^2-3(M-2t)^2)^2(4M^2-3(M-2t)^2) gives the exact polynomial envelope. The defect factors at most three give the stated square bound. This is a necessary-condition lemma for the i=3 reduction; it does not resolve Erdos problem 699.

## References

- Truth anchor: `D5/S3/Arith/Erdos699AdjacentCores.adjacent_core_numerator_bound`
