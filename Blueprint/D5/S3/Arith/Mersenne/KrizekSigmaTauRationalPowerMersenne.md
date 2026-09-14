# Krizek's A046528 Characterization

## Abstract

Krizek's sigma-tau rational-power condition characterizes products of distinct Mersenne primes.

For every positive n, sigma is the divisor-sum function sigma sub one, and tau is the divisor-count function sigma sub zero.

**Definition 1.1 (Products of distinct Mersenne primes).**

$$\forall n \in \mathbb{N},\; isMersenneProduct\left(n\right) \Leftrightarrow \left(\exists S \in Finset\left(\mathbb{N}\right),\; n = \prod_{p \in S} p \land \left(\forall p \in \mathbb{N},\; p \in S \Rightarrow \left(Prime\left(p\right) \land \left(\exists k \in \mathbb{N},\; 0 < k \land p + 1 = 2^{k}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne.isMersenneProduct` (`✓ std3`).

*Citation.* Labos Elemer; Jaroslav Krizek (2013). *OEIS A046528, Numbers that are a product of distinct Mersenne primes*. URL: <https://oeis.org/A046528>.

*Commentary.*

A natural number is a Mersenne product when it is the product over a finite set S of primes p for which p plus one is a positive power of two. The finite set makes the prime factors distinct, and the empty product includes one.

**Definition 1.2 (The sigma-tau integer-power relation).**

$$\forall n \in \mathbb{N},\; ratPow\left(n\right) \Leftrightarrow \left(\exists a \in \mathbb{N}, b \in \mathbb{N},\; 1 \le a \land \left(1 \le b \land sigma\left(n\right)^{b} = tau\left(n\right)^{a}\right)\right)$$

*Formalization.* `D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne.ratPow` (`✓ std3`).

*Citation.* Labos Elemer; Jaroslav Krizek (2013). *OEIS A046528, Numbers that are a product of distinct Mersenne primes*. URL: <https://oeis.org/A046528>.

*Commentary.*

The positive exponents a and b express the rational-power equation without real exponentiation: sigma(n) to b equals tau(n) to a. Here sigma is sigma sub one and tau is sigma sub zero.

**Theorem 1.3 (Krizek's rational-power characterization).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(isMersenneProduct\left(n\right) \Leftrightarrow ratPow\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a046528-sigma-tau-rational-power-mersenne-characterization` (proved) by `D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a046528-sigma-tau-rational-power-mersenne-characterization","declaration_gid":"D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Equality of positive powers gives the same prime support for sigma and tau. A largest-odd-prime argument, geometric sums, multiplicative orders in finite residue fields, and a multiplicity-one calculation force tau to be a power of two. The attributed Sivaramakrishnan-Shallit prerequisite then identifies n as a product of distinct Mersenne primes. Conversely, multiplicativity gives the required exponents. Only this equivalence is proved.

## References

- Truth anchor: `D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne.isMersenneProduct`
- Truth anchor: `D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne.ratPow`
- Truth anchor: `D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne.result`
