# Erdős 699 Denominator Gap

## Abstract

An integral adjacent-column ratio forces a strict denominator gap in the Erdős 699 continuation.

**Theorem 1.1 (Strict gap from an integral ratio).**

$$\forall n \in \mathbb{Z}, L \in \mathbb{Z}, R \in \mathbb{Z}, j \in \mathbb{Z}, m \in \mathbb{Z}, D \in \mathbb{Z}, k \in \mathbb{Z},\; \left(\left(\left(\left(\left(\left(\left(8 \le n \land 0 < R\right) \land 0 < m\right) \land 2 \cdot m < L\right) \land 0 < D\right) \land n - 1 = L \cdot R\right) \land j = 1 + m \cdot R\right) \land D \cdot \left(n - j\right) \cdot \left(n - j - 1\right) = k \cdot \left(n - 1\right) \cdot \left(n - 2\right)\right) \Rightarrow 4 \cdot \left(n - 2\right) < D \cdot L^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Erdos699DenominatorGap.erdos699_denominator_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All seven variables are integers. The hypotheses are exactly n >= 8, R > 0, m > 0, 2m < L, D > 0, n-1 = LR, j = 1+mR, and D(n-j)(n-j-1) = k(n-1)(n-2). No sign assumption is made on k. The conclusion is the strict bound 4(n-2) < DL squared.

Eliminating n and j gives (D(L-m)^2-kL^2)(n-2) = D(L-m)m. The coefficient is a positive integer, so n-2 <= D(L-m)m. The strict inequality 4(L-m)m < L^2 follows from L-2m > 0. This is a symbolic necessary condition. It does not prove any complete p=23,31,89 column or resolve Erdős 699.

## References

- Truth anchor: `D5/S3/Arith/Erdos699DenominatorGap.erdos699_denominator_gap`
