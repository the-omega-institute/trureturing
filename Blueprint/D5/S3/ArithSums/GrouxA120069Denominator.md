# Groux's A120069 denominator equality

## Abstract

The original positive-index Catalan partial sum and its final summand have equal reduced denominators.

Here catalan(k) is Mathlib's ordinary natural Catalan number, characterized by (k+1)catalan(k)=choose(2k,k). Each summand is cast to the rationals before division. The finite interval includes both one and n; subtraction in the exponent is natural subtraction. On this interval k is positive, so k-1 is the source exponent. den is Rat.den, the positive reduced denominator, including den(0)=1.

**Theorem 1.1 (The complete positive-index equality).**

$$\forall n \in \mathbb{N},\; 0 < n \Rightarrow \operatorname{den}\left(\sum_{1 \leq k \leq n} \frac{\operatorname{catalan}\left(k\right)}{4^{k - 1}}\right) = \operatorname{den}\left(\frac{\operatorname{catalan}\left(n\right)}{4^{n - 1}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GrouxA120069Denominator.result` (`✓ std3`). ∎

*Citation.* Groux Roland; Pieter Mostert; OEIS Foundation (2010). *OEIS A120069: Catalan partial-sum denominators*. URL: <https://oeis.org/A120069>.

*Commentary.*

Every positive integer source index corresponds uniquely to a natural n with 0<n. There is no upper bound, recurrence-only replacement, convergence assumption or finite-case surrogate. This is the Groux Roland formula in A120069; the separate A283208 conjecture is outside its scope.

The proof uses the following Catalan form of Pieter Mostert's finite-sum identity from A119951. It is an attributed supplier, proved here by induction from the pinned Catalan/central-binomial relations; it is retained only as a private consumed helper.

$$
\forall n \in \mathbb{N},\; 0 < n \Rightarrow \sum_{1 \leq k \leq n} \frac{\operatorname{catalan}\left(k\right)}{4^{k - 1}} = 4 - \left(2 \cdot n + 1\right) \cdot \frac{\operatorname{catalan}\left(n\right)}{4^{n - 1}}
$$

Put q=catalan(n)/4^(n-1). Its reduced denominator divides 4^(n-1). Since 2n+1 is odd, it is coprime to that denominator. Mathlib's rational multiplication denominator formula therefore gives den((2n+1)q)=den(q). Subtracting from the integer four preserves the denominator, proving the exact equality. The initial index n=1 is included. The argument uses no binary valuation formula for Catalan numbers.

## References

- Truth anchor: `D5/S3/ArithSums/GrouxA120069Denominator.result`
