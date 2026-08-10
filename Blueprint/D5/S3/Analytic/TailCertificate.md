# Finite Sums of Tail Certificates

## Abstract

Finite tail certificates add with summed budgets and enclose the exact sum at every window.

**Theorem 1.1 (Finite tail certificates sum and enclose).**

$$\operatorname{Controlled}(\sum_{i \in s}b_{i}) \land \Vert\sum_{i \in s}v_{i}-\sum_{i \in s}r_{i}(W)\Vert\le\sum_{i \in s}b_{i}(W) \land \sum_{i \in s}r_{i}(W)-\sum_{i \in s}b_{i}(W)\le\sum_{i \in s}v_{i}\le\sum_{i \in s}r_{i}(W)+\sum_{i \in s}b_{i}(W)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/TailCertificate.finite_tail_certificates_sum_and_enclose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family of certificates, the pointwise sum of their budget functions remains controlled. At every window W, the absolute difference between the sum of the exact values and the sum of the window readings is at most the sum of the window budgets. Equivalently, the exact sum lies in the closed interval from the summed reading minus the summed budget to the summed reading plus the summed budget.

## References

- Truth anchor: `D5/S3/Analytic/TailCertificate.finite_tail_certificates_sum_and_enclose`
