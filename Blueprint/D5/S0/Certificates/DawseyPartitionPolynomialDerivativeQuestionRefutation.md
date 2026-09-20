# Dawsey--Russell--Urban Partition Polynomial Derivative Question

## Abstract

The partitions (1,1) and (2) refute the printed derivative-separation question.

**Definition 1.1 (The partition polynomial).**

$$\forall n \in \mathrm{Nat},\; \forall l \in Nat.Partition\left(n\right),\; \operatorname{partitionPolynomial}\left(l\right) = \sum_{i \in \operatorname{parts}\left(l\right)} X^{i}$$

*Formalization.* `D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.partitionPolynomial` (`✓ std3`).

*Citation.* Madeline Locus Dawsey; Tyler Russell; Dannie Urban (2022). *Derivatives and Integrals of Polynomials Associated with Integer Partitions*. DOI: [10.48550/arXiv.2108.00943](https://doi.org/10.48550/arXiv.2108.00943). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL25/Dawsey/dawsey3.pdf>.

*Commentary.*

For a partition l of n, the integer polynomial is the multiset sum of X^i over all parts i of l. Repeated equal parts contribute repeated monomials, so a part i of multiplicity m_i contributes m_i times X^i.

**Definition 1.2 (The largest part).**

$$\forall n \in \mathrm{Nat},\; \forall l \in Nat.Partition\left(n\right),\; \operatorname{largestPart}\left(l\right) = \operatorname{sup}\left(\operatorname{parts}\left(l\right)\right)$$

*Formalization.* `D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.largestPart` (`✓ std3`).

*Citation.* Madeline Locus Dawsey; Tyler Russell; Dannie Urban (2022). *Derivatives and Integrals of Polynomials Associated with Integer Partitions*. DOI: [10.48550/arXiv.2108.00943](https://doi.org/10.48550/arXiv.2108.00943). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL25/Dawsey/dawsey3.pdf>.

*Commentary.*

The value largestPart(l) is the supremum of the multiset of parts, hence the largest part of a nonempty partition and zero for the empty partition of zero.

**Definition 1.3 (Question 9 as printed).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall l \in Nat.Partition\left(n\right),\; \forall r \in Nat.Partition\left(m\right),\; (\operatorname{parts}\left(l\right) \ne \operatorname{parts}\left(r\right)) \Rightarrow (\exists d \in \mathrm{Nat},\; (0 < d) \land \left((d \le \operatorname{min}\left(\operatorname{largestPart}\left(l\right), \operatorname{largestPart}\left(r\right)\right)) \land (\operatorname{partitionPolynomial}\left(l\right)^{(d)}(1) \ne \operatorname{partitionPolynomial}\left(r\right)^{(d)}(1))\right)))$$

*Formalization.* `D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.claim` (`✓ std3`).

*Citation.* Madeline Locus Dawsey; Tyler Russell; Dannie Urban (2022). *Derivatives and Integrals of Polynomials Associated with Integer Partitions*. DOI: [10.48550/arXiv.2108.00943](https://doi.org/10.48550/arXiv.2108.00943). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL25/Dawsey/dawsey3.pdf>.

*Commentary.*

Question 9 asks: "If λ, λ′ are any two unequal partitions, is it true that f_λ^{(d)}(1) ≠ f_{λ′}^{(d)}(1) for some positive integer d ≤ min{lg(λ), lg(λ′)}?" The superscript (d) denotes the d-th formal derivative. The quantifiers permit different sizes and lengths.

**Theorem 1.4 (The printed question has a negative answer).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madeline Locus Dawsey; Tyler Russell; Dannie Urban (2022). *Derivatives and Integrals of Polynomials Associated with Integer Partitions*. DOI: [10.48550/arXiv.2108.00943](https://doi.org/10.48550/arXiv.2108.00943). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL25/Dawsey/dawsey3.pdf>.

*Commentary.*

The unequal partitions (1,1) and (2) both partition 2. Their largest parts are 1 and 2, so the only admissible positive derivative order is 1. Their partition polynomials are 2X and X^2, and both first derivatives evaluate to 2 at 1. This refutes the printed universal assertion and makes no claim about the same-length reading.

## References

- Truth anchor: `D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.claim`
- Truth anchor: `D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.largestPart`
- Truth anchor: `D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.partitionPolynomial`
- Truth anchor: `D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.result`
