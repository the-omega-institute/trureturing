# Zelinsky's Conjecture 1 on prime-factor restrictions

## Abstract

Every fixed prime-factor inequality has positive lower relative density in Euler forms.

**Definition 1.1 (The prime-factor inequality).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.OR`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.OR` (`✓ std3`).

*Citation.* Joshua Zelinsky (2021). *On the Total Number of Prime Factors of an Odd Perfect Number*. URL: <https://math.colgate.edu/~integers/v76/v76.pdf>.

*Commentary.*

For real alpha and beta, OR(alpha,beta)(n) means alpha*omega(n)+beta <= Omega(n). Here omega counts distinct prime factors and Omega counts prime factors with multiplicity, using Mathlib's cardDistinctFactors and cardFactors, respectively. This is the inequality defined on printed page 48 of Section 7.

**Definition 1.2 (Counting the restricted Euler forms).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.orCount`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.orCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2021). *On the Total Number of Prime Factors of an Odd Perfect Number*. URL: <https://math.colgate.edu/~integers/v76/v76.pdf>.

*Commentary.*

orCount(alpha,beta,X) counts integers from 1 to X satisfying EulerForm and OR(alpha,beta). The reused EulerForm predicate says n=q^a*m^2, with q prime, q and a congruent to one modulo four, m positive, and gcd(q,m)=1. It imposes no separate oddness condition on m. Each integer is counted once, regardless of its representations.

**Definition 1.3 (Both clauses of substantially stronger).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.claim`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.claim` (`✓ std3`).

*Citation.* Joshua Zelinsky (2021). *On the Total Number of Prime Factors of an Odd Perfect Number*. URL: <https://math.colgate.edu/~integers/v76/v76.pdf>.

*Commentary.*

Conjecture 1 quantifies over all real alpha1, alpha2, beta1 and beta2 with alpha1 > alpha2 > 2. It asserts both that every Euler form satisfying OR(alpha1,beta1) satisfies OR(alpha2,beta2), and that orCount(alpha1,beta1,X)/orCount(alpha2,beta2,X) tends to zero as the natural threshold X tends to infinity. These are exactly the two requirements of substantially stronger on page 48. Real thresholds have the same counts as their natural-number floors.

**Theorem 1.4 (An upper bound of order X/log(X)).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.euler_count_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.euler_count_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2021). *On the Total Number of Prime Factors of an Odd Perfect Number*. URL: <https://math.colgate.edu/~integers/v76/v76.pdf>.

*Commentary.*

There is a real constant C > 0 such that, for all sufficiently large natural numbers X, eulerCount(X) <= C*X/log(X). The predicate is the full Euler form printed in Section 7: n=q^a*m^2, q prime, q and a congruent to one modulo four, m positive and coprime to q. No parity condition on m is added.

Write a=1+2j and s=q^j*m. Then n=q*s^2. Cover these integers by images of primes q <= X/s^2 for 1 <= s <= floor(X^(1/4)), together with the larger-square tail. Repeated representations only increase this upper bound; no coprimality condition on q and s is imposed.

In the first range X/s^2 >= X^(1/2), so a single Chebyshev threshold applies to every summand for sufficiently large X. Moreover log(X/s^2) >= log(X)/2. The sum of 1/s^2 is at most two. The other range is at most 2X/(T+1), where T=floor(X^(1/4)). Since log(X)/X^(1/4) tends to zero, the tail is eventually at most 2X/log(X). Natural division X/s^2 equals floor((X:real)/s^2), which connects the finite prime counts to the real estimate.

**Theorem 1.5 (A positive lower bound for every parameter pair).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.relative_density_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.relative_density_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2021). *On the Total Number of Prime Factors of an Odd Perfect Number*. URL: <https://math.colgate.edu/~integers/v76/v76.pdf>.

*Commentary.*

For every pair of real numbers alpha and beta, there is a real c > 0 such that c*eulerCount(X) <= orCount(alpha,beta,X) for every sufficiently large natural X. No lower bound on alpha is needed.

Choose an integer h >= 1 with 1+2h >= 2alpha+beta. For every prime q congruent to one modulo four, q differs from 3. Thus 3^(2h)*q has Euler's form with exponent one and square factor 3^h, exactly two distinct prime factors, and 1+2h prime factors with multiplicity. These integers satisfy OR(alpha,beta), and multiplication by 3^(2h) is injective. The modulus-four prime lower bound therefore bounds their count below by a positive multiple of X/log(X).

The full-set estimate counts every Euler form as q*s^2 by absorbing the even part of its prime exponent into the square factor. For s <= X^(1/4), Chebyshev's prime-counting upper bound and the reciprocal-square sum give O(X/log(X)). For larger s, the reciprocal-square tail gives O(X^(3/4)). Consequently eulerCount(X) is at most a constant times X/log(X), and comparison gives the displayed positive relative lower bound.

In particular, the strong-property assertion of Theorem 9 on the same page fails for every alpha > 2 and real beta: its required quotient cannot tend to zero. This concerns counting within the entire printed Euler set, and makes no assertion about the existence of odd perfect numbers.

**Theorem 1.6 (Conjecture 1 is false).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.result` (`✓ std3`). ∎

*Resolves.* `Problems/zelinsky-2021-conjecture-1-or-density` (refuted) by `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zelinsky-2021-conjecture-1-or-density","declaration_gid":"D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2021). *On the Total Number of Prime Factors of an Odd Perfect Number*. URL: <https://math.colgate.edu/~integers/v76/v76.pdf>.

*Commentary.*

Apply the preceding lower bound to (alpha,beta) equal to (4,0) and (3,0). The latter count is at most the full Euler count and eventually positive. Hence the quotient of the former by the latter is eventually bounded below by a positive constant, contradicting the asserted limit zero. For these parameters the inclusion clause itself holds, since omega(n) is nonnegative; the density clause supplies the contradiction.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.OR`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.claim`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.euler_count_upper`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.orCount`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.relative_density_pos`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.result`
- Dependency: [D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity](StrongPseudoperfectEulerDensity.md)
