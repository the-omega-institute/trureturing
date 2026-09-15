# Erdos's Consecutive-Product Factor Question

## Abstract

The starting value 47 refutes the proposed uniqueness of 23 among starting values whose consecutive products always have dominant repeated factors.

**Definition 1.1 (The consecutive product).**

$$\forall x \in \mathrm{Nat}, k \in \mathrm{Nat},\; P\left(x, k\right) = \prod_{i \in Icc\left(1, k\right)} (x + i)$$

*Formalization.* `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.P` (`✓ std3`).

*Citation.* Paul Erdős (1985). *Problems and results on consecutive integers and prime factors of binomial coefficients*. DOI: [10.1216/RMJ-1985-15-2-353](https://doi.org/10.1216/RMJ-1985-15-2-353).

*Commentary.*

P(x,k) is the product of the k consecutive integers immediately after x.

**Definition 1.2 (The single-exponent factor).**

$$\forall x \in \mathrm{Nat}, k \in \mathrm{Nat},\; v\left(x, k\right) = \prod_{p \in \{p \in primeFactors\left(P\left(x, k\right)\right) \mid factorization\left(P\left(x, k\right)\right)\left(p\right) = 1\}} p$$

*Formalization.* `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.v` (`✓ std3`).

*Citation.* Paul Erdős (1985). *Problems and results on consecutive integers and prime factors of binomial coefficients*. DOI: [10.1216/RMJ-1985-15-2-353](https://doi.org/10.1216/RMJ-1985-15-2-353).

*Commentary.*

The factor v(x,k) is the product of exactly those primes whose exponent in P(x,k) equals one. It is not the squarefree part of P(x,k).

**Definition 1.3 (The repeated-prime-power factor).**

$$\forall x \in \mathrm{Nat}, k \in \mathrm{Nat},\; u\left(x, k\right) = \prod_{p \in \{p \in primeFactors\left(P\left(x, k\right)\right) \mid 2 \le factorization\left(P\left(x, k\right)\right)\left(p\right)\}} p^{factorization\left(P\left(x, k\right)\right)\left(p\right)}$$

*Formalization.* `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.u` (`✓ std3`).

*Citation.* Paul Erdős (1985). *Problems and results on consecutive integers and prime factors of binomial coefficients*. DOI: [10.1216/RMJ-1985-15-2-353](https://doi.org/10.1216/RMJ-1985-15-2-353).

*Commentary.*

The factor u(x,k) contains each prime power whose exponent in P(x,k) is at least two, with that full exponent.

**Definition 1.4 (The proposed uniqueness of 23).**

$$(claim) \Leftrightarrow (\forall x \in \mathrm{Nat},\; (1 \le x) \Rightarrow \left((x \ne 23) \Rightarrow (\exists k \in \mathrm{Nat},\; (1 \le k) \land (u\left(x, k\right) < v\left(x, k\right)))\right))$$

*Formalization.* `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.claim` (`✓ std3`).

*Citation.* Paul Erdős (1985). *Problems and results on consecutive integers and prime factors of binomial coefficients*. DOI: [10.1216/RMJ-1985-15-2-353](https://doi.org/10.1216/RMJ-1985-15-2-353).

*Commentary.*

Every positive starting value other than 23 is asserted to admit a positive length for which the single-exponent factor exceeds the repeated factor.

**Theorem 1.5 (The starting value 47 is another exception).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/erdos-1985-consecutive-product-squarefree-factor-refutation` (refuted) by `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"erdos-1985-consecutive-product-squarefree-factor-refutation","declaration_gid":"D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul Erdős (1985). *Problems and results on consecutive integers and prime factors of binomial coefficients*. DOI: [10.1216/RMJ-1985-15-2-353](https://doi.org/10.1216/RMJ-1985-15-2-353).

*Commentary.*

For x=47, direct factor-exponent arguments handle lengths 1 through 78. For every length at least 79, an inductive exponential lower bound for P combines with the primorial upper bound for v to give v<u. This leaves conjecture (22) and the statement about x=23 untouched.

## References

- Truth anchor: `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.P`
- Truth anchor: `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.claim`
- Truth anchor: `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.result`
- Truth anchor: `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.u`
- Truth anchor: `D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.v`
