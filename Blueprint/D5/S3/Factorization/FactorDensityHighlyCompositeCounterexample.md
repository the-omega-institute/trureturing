# Factor-Density and Highly Composite Counterexample

## Abstract

A finite exponent-profile certificate and an exact power inequality refute the expanded factor-density coincidence claim at 73329656400.

**Definition 1.1 (Divisor-count function).**

$$\forall n \in \mathbb{N},\; \operatorname{tau}\left(n\right) = \operatorname{card}\left(\operatorname{divisors}\left(n\right)\right)$$

*Formalization.* `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.tau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural number n, tau(n) is the cardinality of Nat.divisors n. This is the divisor-count function used in both record predicates.

**Definition 1.2 (Expanded factor-density score).**

$$\forall n \in \mathbb{N},\; \operatorname{g}\left(n\right) = \frac{\operatorname{val}\left(\operatorname{tau}\left(n\right)\right)}{\operatorname{log}\left(\operatorname{val}\left(n\right) + 1\right)}$$

*Formalization.* `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.g` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The numerator and n are explicitly cast from natural numbers to real numbers. The displayed fraction is real division, matching tau(n)/log(n+1); no natural-number division occurs in this module. This repository formula transcribes Switkay's expanded score from the cited OEIS comment.

**Definition 1.3 (Expanded factor-density record predicate).**

$$\forall n \in \mathbb{N},\; \operatorname{FD}\left(n\right) \Leftrightarrow \left(\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \left(m < n \Rightarrow \operatorname{g}\left(m\right) < \operatorname{g}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.FD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FD(n) requires every natural m with 1 <= m and m < n to have strictly smaller expanded score g(m). The nested implications mirror the Lean definition.

**Definition 1.4 (Highly composite record predicate).**

$$\forall n \in \mathbb{N},\; \operatorname{HC}\left(n\right) \Leftrightarrow \left(\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \left(m < n \Rightarrow \operatorname{tau}\left(m\right) < \operatorname{tau}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.HC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HC(n) requires every natural m with 1 <= m and m < n to have strictly smaller divisor count tau(m).

**Definition 1.5 (Counterexample candidate).**

$$N = 73329656400$$

*Formalization.* `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.N` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N names the explicit highly composite candidate 73329656400.

**Definition 1.6 (Smaller comparison witness).**

$$M = 64250746560$$

*Formalization.* `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M names the smaller integer whose factor-density score exceeds that of N.

**Definition 1.7 (First eleven primes).**

$$primes11 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]$$

*Formalization.* `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.primes11` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This exact list supplies the coordinatewise lower bound for eleven sorted distinct prime factors. Its product is 200560490130, above 73329656400.

**Definition 1.8 (First ten primes).**

$$\begin{aligned}primes10 = \operatorname{take}\left(10, primes11\right)\\primes10 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]\end{aligned}$$

*Formalization.* `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.primes10` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

primes10 is List.take 10 primes11 and therefore has the displayed ten entries. These are the bases of every profile admitted by the checker.

**Definition 1.9 (Pruned exponent-profile checker).**

$$\begin{aligned}profileCheck: \operatorname{List}\left(\mathbb{N}\right) \to \mathbb{N} \to \mathbb{N} \to Bool\\\forall v \in \mathbb{N}, t \in \mathbb{N},\; \operatorname{profileCheck}\left([], v, t\right) = \operatorname{decide}\left(t \le 3584\right)\\\forall p \in \mathbb{N}, ps \in \operatorname{List}\left(\mathbb{N}\right), v \in \mathbb{N}, t \in \mathbb{N},\; \operatorname{profileCheck}\left(\operatorname{cons}\left(p, ps\right), v, t\right) = \operatorname{decide}\left(t \le 3584\right) \land \operatorname{all}\left(\operatorname{takeWhile}\left(\operatorname{List.range'}\left(1, 36\right), (e: \mathbb{N} \mapsto \operatorname{decide}\left(v \cdot p^{e} < 73329656400\right))\right), (e: \mathbb{N} \mapsto \operatorname{profileCheck}\left(ps, v \cdot p^{e}, t \cdot \left(e + 1\right)\right))\right)\end{aligned}$$

*Formalization.* `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.profileCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The checker recurses on the prime-base list. Its empty branch tests t <= 3584. For p :: ps it first tests the same divisor-product bound, then checks every e in the consecutive range 1 through 36 while v*p^e < 73329656400, recursing at value v*p^e and divisor product t*(e+1).

The takeWhile pruning is sound because the bases are positive and powers grow with the exponent. The subsequent proof maps arbitrary sorted prime factors coordinatewise onto these smaller prime bases.

**Theorem 1.10 (Prime factorization of the counterexample candidate).**

$$N = 2^{4} \cdot 3^{4} \cdot 5^{2} \cdot 7^{2} \cdot 11 \cdot 13 \cdot 17 \cdot 19$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.N_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is the exact prime factorization of N.

**Theorem 1.11 (Prime factorization of the comparison witness).**

$$M = 2^{6} \cdot 3^{3} \cdot 5 \cdot 7 \cdot 11 \cdot 13 \cdot 17 \cdot 19 \cdot 23$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.M_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is the exact prime factorization of M.

**Theorem 1.12 (Exact divisor count of the counterexample candidate).**

$$\operatorname{tau}\left(N\right) = 3600$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.tau_N` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorization of N gives the exact divisor count tau(N)=3600.

**Theorem 1.13 (Exact divisor count of the comparison witness).**

$$\operatorname{tau}\left(M\right) = 3584$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.tau_M` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorization of M gives the exact divisor count tau(M)=3584.

**Theorem 1.14 (Kernel profile certificate).**

$$\operatorname{profileCheck}\left(primes10, 1, 1\right) = true$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.profile_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lean's kernel evaluates the checker with maxRecDepth 100000 and unlimited heartbeats. A separate deterministic recount records 22091 reachable positive-exponent prefix profiles; the theorem itself is the exact Boolean equality.

**Theorem 1.15 (Divisor-count bound below the candidate).**

$$\forall m \in \mathbb{N},\; 0 < m \Rightarrow \left(m < N \Rightarrow \operatorname{tau}\left(m\right) \le 3584\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.tau_lt_N_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The profile certificate proves tau(m) <= 3584 for every positive m below N.

**Theorem 1.16 (The candidate is highly composite).**

$$\operatorname{HC}\left(N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.hc_N` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The predecessor bound and tau(N)=3600 prove that every positive predecessor has strictly fewer divisors than N.

**Theorem 1.17 (Exact power inequality).**

$$64250746561^{225} < 73329656401^{224}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.power_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This natural-number inequality is kernel reduced. Monotonicity and the power law for the real logarithm transport it to the strict comparison g(73329656400) < g(64250746560).

**Theorem 1.18 (The candidate has smaller factor density).**

$$\operatorname{g}\left(N\right) < \operatorname{g}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.g_N_lt_g_M` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The power witness, tau(N)=3600, and tau(M)=3584 yield the strict score comparison g(N)<g(M).

**Theorem 1.19 (The candidate is not factor dense).**

$$\neg (\operatorname{FD}\left(N\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.not_fd_N` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Because M<N while g(N)<g(M), N fails the expanded factor-density record predicate.

**Theorem 1.20 (The candidate is not the exceptional value).**

$$N \ne 45360$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.N_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact arithmetic separates N from the claimed exceptional value 45360.

**Theorem 1.21 (Explicit factor-density counterexample).**

$$\operatorname{HC}\left(N\right) \land \left(N \ne 45360 \land \neg (\operatorname{FD}\left(N\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.factor_density_highly_composite_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sorted-prime lower bound shows that every positive m below 73329656400 has at most ten distinct prime factors, each exponent lies from 1 through 36, and the successful profile certificate bounds tau(m) by 3584. Exact factorization gives tau(73329656400)=3600, proving HC.

The smaller witness M=64250746560 has tau(M)=3584. The power witness and real logarithm laws prove g(73329656400)<g(M), so 73329656400 is not an FD record. The remaining inequality 73329656400 != 45360 is exact arithmetic.

**Theorem 1.22 (Switkay's expanded coincidence claim is false).**

$$\neg (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\operatorname{FD}\left(n\right) \Leftrightarrow \left(\operatorname{HC}\left(n\right) \land n \ne 45360\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.switkay_expanded_claim_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hal M. Switkay's OEIS A399133 comment dated 2026-08-19 states: "All these numbers are highly composite (A002182) and even factor-dense (A210594) under the expanded definition of factor-density given in the comments. However, factor-density appears to coincide with being highly composite other than at 45360." The theorem refutes that expanded-definition assertion here.

The expanded definition is g(n)=tau(n)/log(1+n), as stated in Switkay's 2022-09-07 OEIS A210594 comment. The A210594 b-file already omits this N under the original (tau(n)-1)/log(n) definition; this result claims only the exact kernel refutation of the later expanded-definition assertion. First-publication priority is ASSUMED-UNVERIFIED.

## References

- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.FD`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.HC`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.M`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.M_factorization`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.N`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.N_factorization`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.N_ne`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.factor_density_highly_composite_counterexample`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.g`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.g_N_lt_g_M`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.hc_N`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.not_fd_N`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.power_witness`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.primes10`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.primes11`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.profileCheck`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.profile_certificate`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.switkay_expanded_claim_false`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.tau`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.tau_M`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.tau_N`
- Truth anchor: `D5/S3/Factorization/FactorDensityHighlyCompositeCounterexample.tau_lt_N_bound`
- Dependency: [D5/S3/Arith/PrimitiveRoot/SievePrimeFactors](../Arith/PrimitiveRoot/SievePrimeFactors.md)
