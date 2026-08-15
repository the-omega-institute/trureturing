# Fourier-Matrix Defect and Divisor Supply

## Abstract

The arithmetic defect of a Fourier matrix is supplied by its nontrivial divisors.

**Theorem 1.1 (Fourier-matrix defect is supplied by nontrivial divisors).**

$$\forall n\in\mathbb{N},\ n\geq2 \Rightarrow \left(\operatorname{defect}(F_{n}) = \sum_{d\mid n, d>1} \varphi(d)(\frac{n}{d}-1) \land (\operatorname{defect}(F_{n}) = 0 \Leftrightarrow \operatorname{Prime}(n))\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/FourierMatrixDefect.fourier_defect_factor_supply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least two, define the arithmetic Fourier defect as the sum of gcd(n,k)-1 over 1 <= k < n. Grouping residues by their gcd with n shows that a divisor d contributes phi(d) copies of n/d-1 after the divisor involution d maps to n/d. Removing k=0 on the residue side cancels the d=1 contribution on the divisor side.

The source's divisor sum is read over nontrivial divisors. This is the only reading compatible with its same-clause assertion that the defect vanishes at prime orders: including d=1 would contribute n-1. The Lean statement records both the exact factor-supply formula and the prime vanishing criterion, with the lower bound n >= 2 explicit.

The pinned library search found Nat.totient_div_of_dvd as the exact gcd fiber count and Nat.sum_div_divisors as the exact divisor reindexing; both are imported and applied. Loogle found no theorem matching the complete identity, LeanSearch was unavailable locally, and repository searches found no declaration with this statement.

The converse is substantive: if n is composite, mathlib supplies a proper divisor d with 2 <= d < n. Its k=d summand is d-1 > 0, contradicting zero defect. For prime n the divisor set is exactly {1,n}, and the sole nontrivial-divisor summand vanishes.

## References

- Truth anchor: `D5/S3/QuantumContext/FourierMatrixDefect.fourier_defect_factor_supply`
