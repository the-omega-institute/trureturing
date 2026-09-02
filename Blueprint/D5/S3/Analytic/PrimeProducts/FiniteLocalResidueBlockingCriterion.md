# Finite Local Residue Blocking Criterion

## Abstract

A finite offset set can cover every residue class only at primes no larger than the number of offsets.

**Theorem 1.1 (Only finitely many primes can completely block an offset set).**

$$\forall H \in \operatorname{Finset}\left(\mathbb{Z}\right), k \in \mathbb{N},\; \left|H\right| = k \Rightarrow \left(\left(\forall p \in NatPrimes,\; k < p \Rightarrow \left(\left(\nu_{p}\right)\left(H\right) \le k \land \left(\nu_{p}\right)\left(H\right) < p\right)\right) \land \left(\left(\forall p \in NatPrimes,\; \left(\nu_{p}\right)\left(H\right) < p\right) \Leftrightarrow \left(\forall p \in NatPrimes,\; p \le k \Rightarrow \left(\nu_{p}\right)\left(H\right) < p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FiniteLocalResidueBlockingCriterion.finite_local_residue_blocking_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite set H of integer offsets, the local residue set modulo p is constructed as the image of h mapped to minus h in ZMod p. The local residue count nu_p(H) is its cardinality.

The image has at most the cardinality k of H. Thus every prime p larger than k has nu_p(H) strictly below p and cannot be a complete residue obstruction.

It follows that admissibility over all primes is equivalent to the same inequality restricted to primes at most k. This reduction concerns complete blocking only; the later numerical singular series retains its all-prime index.

## References

- Truth anchor: `D5/S3/Analytic/PrimeProducts/FiniteLocalResidueBlockingCriterion.finite_local_residue_blocking_criterion`
