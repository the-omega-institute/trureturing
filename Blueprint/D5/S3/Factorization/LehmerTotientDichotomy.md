# Lehmer Totient Divisibility Dichotomy

## Abstract

Lehmer's totient divisibility condition yields a prime/composite structural dichotomy.

**Definition 1.1 (Korselt's local divisibility condition).**

$$\forall n: \mathbb{N},\\{}\operatorname{IsKorselt}\left(n\right) := \operatorname{Squarefree}\left(n\right) \land \forall p \in \operatorname{primeFactors}\left(n\right), p - 1 \mid n - 1.$$

*Formalization.* `D5/S3/Factorization/LehmerTotientDichotomy.IsKorselt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsKorselt records squarefreeness together with divisibility of n - 1 by p - 1 for every prime divisor p of n.

**Theorem 1.2 (A repeated prime factor enters the totient).**

$$\forall p, n \in \mathbb{N},\\{}\operatorname{Prime}\left(p\right) \land {p}^{2} \mid n \Rightarrow p \mid \operatorname{totient}\left(n\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.prime_dvd_totient_of_sq_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The totient of p squared is p times p - 1. Totient divisibility under divisibility then transports the factor p from p squared to n.

**Theorem 1.3 (Lehmer divisibility forces squarefreeness).**

$$\forall n: \mathbb{N}, 1 < n \land \operatorname{totient}\left(n\right) \mid n - 1 \Rightarrow \operatorname{Squarefree}\left(n\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.squarefree_of_totient_dvd_pred` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If p squared divided n, then p would divide both n and n - 1 through the totient hypothesis. This would force p to divide one.

**Theorem 1.4 (The squarefree totient is a prime-factor product).**

$$\forall n: \mathbb{N},\\{}n \neq 0 \land \operatorname{Squarefree}\left(n\right) \Rightarrow \operatorname{totient}\left(n\right) = \prod_{p \in \operatorname{primeFactors}\left(n\right)} {p - 1}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.totient_eq_prod_primeFactors_sub_one_of_squarefree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen SieveCoefficients theorem proves the displayed product identity from squarefreeness alone, so the nonzero assumption is retained only to mirror the source obligation.

**Theorem 1.5 (The composite branch is odd).**

$$\forall n: \mathbb{N},\\{}1 < n \land \operatorname{totient}\left(n\right) \mid n - 1 \land \neg \operatorname{Prime}\left(n\right) \Rightarrow \operatorname{Odd}\left(n\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.odd_of_totient_dvd_pred_of_not_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A composite n greater than one has even totient. If n were even as well, two would divide both n and n - 1, hence one.

**Theorem 1.6 (The prime-factor product divides the predecessor).**

$$\forall n: \mathbb{N},\\{}1 < n \land \operatorname{totient}\left(n\right) \mid n - 1 \Rightarrow \prod_{p \in \operatorname{primeFactors}\left(n\right)} {p - 1} \mid n - 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.prod_primeFactors_sub_one_dvd_pred` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squarefreeness identifies the displayed product with the totient, so the assumed divisibility transfers to the product.

**Theorem 1.7 (Lehmer divisibility implies the Korselt condition).**

$$\forall n: \mathbb{N},\\{}1 < n \land \operatorname{totient}\left(n\right) \mid n - 1 \Rightarrow \operatorname{IsKorselt}\left(n\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.isKorselt_of_totient_dvd_pred` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each p - 1 is a factor of the squarefree totient product, which divides n - 1; the preceding theorem supplies squarefreeness.

**Theorem 1.8 (The prime-factor count supplies a power of two).**

$$\forall n: \mathbb{N},\\{}1 < n \land \operatorname{totient}\left(n\right) \mid n - 1 \land \neg \operatorname{Prime}\left(n\right) \Rightarrow 2^{\operatorname{card}\left(\operatorname{primeFactors}\left(n\right)\right)} \mid n - 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.two_pow_card_primeFactors_dvd_pred` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prime factor on the odd composite branch is odd, so each p - 1 contributes a factor of two to the totient product.

**Theorem 1.9 (The composite branch has at least three prime factors).**

$$\forall n: \mathbb{N},\\{}1 < n \land \operatorname{totient}\left(n\right) \mid n - 1 \land \neg \operatorname{Prime}\left(n\right) \Rightarrow 3 \le \operatorname{card}\left(\operatorname{primeFactors}\left(n\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.three_le_card_primeFactors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squarefreeness excludes a prime power. The remaining two-factor case would make (p - 1)(q - 1) divide pq - 1, but a direct estimate forces the quotient to be one and yields a contradiction.

**Theorem 1.10 (Prime or full composite structural package).**

$$\begin{gathered}\forall n: \mathbb{N},\\{}1 < n \land \operatorname{totient}\left(n\right) \mid n - 1 \Rightarrow\\{}\operatorname{Prime}\left(n\right) \lor {\operatorname{Odd}\left(n\right) \land \operatorname{Squarefree}\left(n\right) \land \operatorname{IsKorselt}\left(n\right) \land\\{}\prod_{p \in \operatorname{primeFactors}\left(n\right)} {p - 1} \mid n - 1 \land\\{}2^{\operatorname{card}\left(\operatorname{primeFactors}\left(n\right)\right)} \mid n - 1 \land\\{}3 \le \operatorname{card}\left(\operatorname{primeFactors}\left(n\right)\right)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/LehmerTotientDichotomy.totient_dvd_pred_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A number satisfying the totient divisibility condition is prime, or it is odd, squarefree, Korselt, satisfies the product divisibility, carries the full two-adic factor, and has at least three distinct prime factors.

## References

- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.IsKorselt`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.isKorselt_of_totient_dvd_pred`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.odd_of_totient_dvd_pred_of_not_prime`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.prime_dvd_totient_of_sq_dvd`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.prod_primeFactors_sub_one_dvd_pred`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.squarefree_of_totient_dvd_pred`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.three_le_card_primeFactors`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.totient_dvd_pred_dichotomy`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.totient_eq_prod_primeFactors_sub_one_of_squarefree`
- Truth anchor: `D5/S3/Factorization/LehmerTotientDichotomy.two_pow_card_primeFactors_dvd_pred`
