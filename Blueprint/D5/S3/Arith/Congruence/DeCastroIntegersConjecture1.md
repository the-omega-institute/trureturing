# DeCastroIntegersConjecture1

## Abstract

Prime-power denominator saturation proves de Castro’s admissible-fraction formula.

**Definition 1.1 (The binomial fraction).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{frac}\left(n, k\right) = \frac{1}{(n : \mathbb{Q})} \cdot (\operatorname{Nat}.\operatorname{choose}\left(n, k\right) : \mathbb{Q})$$

*Formalization.* `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.frac` (`✓ std3`).

*Citation.* Dario T. de Castro (2022). *p-Adic order of positive integers via binomial coefficients*. URL: <https://math.colgate.edu/~integers/w61/w61.pdf>.

*Commentary.*

Definition 2 (p. 7): “Let S^min_{p,n} and S^max_{p,n} denote sets of irreducible fractions given by S^min_{p,n} = {(1/n) binomial(n, p_i^j) | i ∈ N*, j ∈ N, gcd(p_i^j, p) = 1, p_i^j ≤ n}, S^max_{p,n} = {(1/n) binomial(n, k) | 0 < k ≤ n, gcd(k, p) = 1}.” The rational number (1/n) binomial(n,k) is the fraction used in both sets.

**Definition 1.2 (The lower set of fractions).**

$$\forall p \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{Smin}\left(p, n\right) = \{(x : \mathbb{Q}) | \exists i \in \mathbb{N},\; \exists j \in \mathbb{N},\; 1 \le i \land \left(\operatorname{Nat}.\operatorname{gcd}\left(\operatorname{Nat}.\operatorname{nth}\left(\operatorname{Nat}.\operatorname{Prime}, i - 1\right)^{j}, p\right) = 1 \land \left(\operatorname{Nat}.\operatorname{nth}\left(\operatorname{Nat}.\operatorname{Prime}, i - 1\right)^{j} \le n \land x = \frac{1}{(n : \mathbb{Q})} \cdot (\operatorname{Nat}.\operatorname{choose}\left(n, \operatorname{Nat}.\operatorname{nth}\left(\operatorname{Nat}.\operatorname{Prime}, i - 1\right)^{j}\right) : \mathbb{Q})\right)\right)\}$$

*Formalization.* `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.Smin` (`✓ std3`).

*Citation.* Dario T. de Castro (2022). *p-Adic order of positive integers via binomial coefficients*. URL: <https://math.colgate.edu/~integers/w61/w61.pdf>.

*Commentary.*

Definition 2 (p. 7): “Let S^min_{p,n} and S^max_{p,n} denote sets of irreducible fractions given by S^min_{p,n} = {(1/n) binomial(n, p_i^j) | i ∈ N*, j ∈ N, gcd(p_i^j, p) = 1, p_i^j ≤ n}, S^max_{p,n} = {(1/n) binomial(n, k) | 0 < k ≤ n, gcd(k, p) = 1}.” The i-th prime is Nat.nth Nat.Prime (i-1), with i ≥ 1 and j ≥ 0. Subtraction of indices is in the natural numbers.

**Definition 1.3 (The upper set of fractions).**

$$\forall p \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{Smax}\left(p, n\right) = \{(x : \mathbb{Q}) | \exists k \in \mathbb{N},\; 0 < k \land \left(k \le n \land \left(\operatorname{Nat}.\operatorname{gcd}\left(k, p\right) = 1 \land x = \frac{1}{(n : \mathbb{Q})} \cdot (\operatorname{Nat}.\operatorname{choose}\left(n, k\right) : \mathbb{Q})\right)\right)\}$$

*Formalization.* `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.Smax` (`✓ std3`).

*Citation.* Dario T. de Castro (2022). *p-Adic order of positive integers via binomial coefficients*. URL: <https://math.colgate.edu/~integers/w61/w61.pdf>.

*Commentary.*

Definition 2 (p. 7): “Let S^min_{p,n} and S^max_{p,n} denote sets of irreducible fractions given by S^min_{p,n} = {(1/n) binomial(n, p_i^j) | i ∈ N*, j ∈ N, gcd(p_i^j, p) = 1, p_i^j ≤ n}, S^max_{p,n} = {(1/n) binomial(n, k) | 0 < k ≤ n, gcd(k, p) = 1}.” Fractions are elements of the rationals in lowest terms.

**Definition 1.4 (Conjecture 1).**

$$\operatorname{claim} = (\forall p \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(1 \le n \Rightarrow \left(\forall S \in \operatorname{Finset}\left(\mathbb{Q}\right),\; \left(\operatorname{Smin}\left(p, n\right) \subseteq (S : \operatorname{Set}\left(\mathbb{Q}\right)) \land (S : \operatorname{Set}\left(\mathbb{Q}\right)) \subseteq \operatorname{Smax}\left(p, n\right)\right) \Rightarrow (\operatorname{padicValNat}\left(p, n\right) : \mathbb{R}) = \operatorname{Real}.\operatorname{logb}\left((p : \mathbb{R}), \frac{(n : \mathbb{R})}{(\operatorname{Finset}.\operatorname{lcm}\left(S, \operatorname{Rat}.\operatorname{den}\right) : \mathbb{R})}\right)\right)\right))$$

*Formalization.* `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.claim` (`✓ std3`).

*Citation.* Dario T. de Castro (2022). *p-Adic order of positive integers via binomial coefficients*. URL: <https://math.colgate.edu/~integers/w61/w61.pdf>.

*Commentary.*

Conjecture 1 (p. 7): “Given any admissible set S_{p,n}, the p-adic order of a positive integer n can be expressed as v_p(n) = log_p(n / L_{p,n}), where L_{p,n} represents the least common denominator of the elements of S_{p,n}.” The order is padicValNat, the logarithm is Real.logb, and the least common denominator is Finset.lcm applied to Rat.den. Natural values are explicitly cast to the reals.

**Lemma 1.5 (The denominator divides the lower binomial index).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; 0 < n \Rightarrow \left(0 < k \Rightarrow \operatorname{Rat}.\operatorname{den}\left(\operatorname{frac}\left(n, k\right)\right) \mid k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.den_dvd_k` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dario T. de Castro (2022). *p-Adic order of positive integers via binomial coefficients*. URL: <https://math.colgate.edu/~integers/w61/w61.pdf>.

*Commentary.*

For positive n and k, the identity binomial(n,k)/n = binomial(n-1,k-1)/k bounds the reduced denominator by k.

**Lemma 1.6 (The common divisor bound).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; 0 < n \Rightarrow \left(0 < k \Rightarrow \operatorname{Rat}.\operatorname{den}\left(\operatorname{frac}\left(n, k\right)\right) \mid \operatorname{Nat}.\operatorname{gcd}\left(n, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.den_dvd_gcd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dario T. de Castro (2022). *p-Adic order of positive integers via binomial coefficients*. URL: <https://math.colgate.edu/~integers/w61/w61.pdf>.

*Commentary.*

For positive n and k, the reduced denominator divides gcd(n,k). This bound also applies to composite bases.

**Lemma 1.7 (Saturation at a prime-power divisor).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall j \in \mathbb{N},\; 0 < n \Rightarrow \left(\operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(p^{j} \mid n \Rightarrow \operatorname{Rat}.\operatorname{den}\left(\operatorname{frac}\left(n, p^{j}\right)\right) = p^{j}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.den_prime_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dario T. de Castro (2022). *p-Adic order of positive integers via binomial coefficients*. URL: <https://math.colgate.edu/~integers/w61/w61.pdf>.

*Commentary.*

If a prime power p^j divides positive n, the binomial fraction at index p^j has denominator exactly p^j. The exponent j=0 is included. Lucas congruences show that the shifted binomial numerator is prime to p.

**Lemma 1.8 (The logarithmic equation as a natural identity).**

$$\forall q \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall l \in \mathbb{N},\; \forall e \in \mathbb{N},\; 1 < q \Rightarrow \left(0 < n \Rightarrow \left(0 < l \Rightarrow \left((e : \mathbb{R}) = \operatorname{Real}.\operatorname{logb}\left((q : \mathbb{R}), \frac{(n : \mathbb{R})}{(l : \mathbb{R})}\right) \Leftrightarrow q^{e} \cdot l = n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.logarithm_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dario T. de Castro (2022). *p-Adic order of positive integers via binomial coefficients*. URL: <https://math.colgate.edu/~integers/w61/w61.pdf>.

*Commentary.*

For q>1 and positive n and l, the real logarithmic equation is equivalent to q^e*l=n in the naturals.

**Theorem 1.9 (De Castro Conjecture 1).**

$$\forall p \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow \left(1 \le n \Rightarrow \left(\forall S \in \operatorname{Finset}\left(\mathbb{Q}\right),\; \left(\operatorname{Smin}\left(p, n\right) \subseteq (S : \operatorname{Set}\left(\mathbb{Q}\right)) \land (S : \operatorname{Set}\left(\mathbb{Q}\right)) \subseteq \operatorname{Smax}\left(p, n\right)\right) \Rightarrow (\operatorname{padicValNat}\left(p, n\right) : \mathbb{R}) = \operatorname{Real}.\operatorname{logb}\left((p : \mathbb{R}), \frac{(n : \mathbb{R})}{(\operatorname{Finset}.\operatorname{lcm}\left(S, \operatorname{Rat}.\operatorname{den}\right) : \mathbb{R})}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dario T. de Castro (2022). *p-Adic order of positive integers via binomial coefficients*. URL: <https://math.colgate.edu/~integers/w61/w61.pdf>.

*Commentary.*

The prime-power fractions in Smin provide every prime-power divisor of n away from p. The gcd bound excludes p and any larger denominator, so the lcm is n.divMaxPow p. The factorization of n then gives the logarithmic equation.

## References

- Truth anchor: `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.Smax`
- Truth anchor: `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.Smin`
- Truth anchor: `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.claim`
- Truth anchor: `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.den_dvd_gcd`
- Truth anchor: `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.den_dvd_k`
- Truth anchor: `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.den_prime_pow`
- Truth anchor: `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.frac`
- Truth anchor: `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.logarithm_iff`
- Truth anchor: `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.result`
