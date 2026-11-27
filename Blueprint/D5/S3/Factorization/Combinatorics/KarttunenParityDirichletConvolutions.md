# The two A369255 Dirichlet convolutions

## Abstract

The two A369255 Dirichlet convolutions.

**Definition 1.1 (Divisors at most the square root).**

$$\forall n \in Nat,\; \operatorname{g}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun (d:Nat) \mapsto d \cdot d \le n), (\operatorname{Nat}.\operatorname{divisors}\left(n\right))\right)\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.g` (`✓ std3`).

*Citation.* Antti Karttunen; Sequence Machine (2024). *OEIS A369255, two Dirichlet convolution conjectures*. URL: <https://oeis.org/A369255/internal>.

*Commentary.*

OEIS A038548, revision 195, NAME (unpaginated). “Number of divisors of n that are at most sqrt(n).” For positive n the condition d * d ≤ n retains the divisor on the diagonal when n is a square.

**Definition 1.2 (Unordered coprime factor pairs).**

$$\forall n \in Nat,\; \operatorname{A}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun (rs:Nat \times Nat) \mapsto \operatorname{Prod}.\operatorname{fst}\left(rs\right) \le \operatorname{Prod}.\operatorname{snd}\left(rs\right) \land \operatorname{Nat}.\operatorname{Coprime}\left((\operatorname{Prod}.\operatorname{fst}\left(rs\right)), (\operatorname{Prod}.\operatorname{snd}\left(rs\right))\right)), (\operatorname{Nat}.\operatorname{divisorsAntidiagonal}\left(n\right))\right)\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.A` (`✓ std3`).

*Citation.* Antti Karttunen; Sequence Machine (2024). *OEIS A369255, two Dirichlet convolution conjectures*. URL: <https://oeis.org/A369255/internal>.

*Commentary.*

OEIS A007875, revision 82, NAME (unpaginated). “Number of ways of writing n as p*q, with p <= q, gcd(p, q) = 1.” The two factors are positive. The pair (1,1) contributes at n = 1.

**Definition 1.3 (Möbius convolution with the fourth-power indicator).**

$$\forall n \in Nat,\; \operatorname{B}\left(n\right) = \operatorname{Finset}.\operatorname{sum}\left((\operatorname{Nat}.\operatorname{divisors}\left(n\right)), (fun (d:Nat) \mapsto if (d^{4} \mid n) then \operatorname{ArithmeticFunction}.\operatorname{moebius}\left((\operatorname{Nat}.\operatorname{div}\left(n, d^{4}\right))\right) else 0)\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.B` (`✓ std3`).

*Citation.* Antti Karttunen; Sequence Machine (2024). *OEIS A369255, two Dirichlet convolution conjectures*. URL: <https://oeis.org/A369255/internal>.

*Commentary.*

OEIS A219009, revision 44, program line (unpaginated). “a(n)=sumdiv(n,d,if(issquare(d),issquare(sqrtint(d)),0)*moebius(n/d))” Index each fourth-power divisor by its positive fourth root. Nat.div computes the quotient exactly on the branch where the fourth power divides n.

**Definition 1.4 (The multiplicative prime-power prescription).**

$$\forall n \in Nat,\; \operatorname{C}\left(n\right) = \operatorname{Finset}.\operatorname{prod}\left((\operatorname{Nat}.\operatorname{primeFactors}\left(n\right)), (fun (p:Nat) \mapsto (2:Int) \cdot ((\operatorname{Nat}.\operatorname{mod}\left(((\operatorname{Nat}.\operatorname{factorization}\left(n, p\right))), 2\right)):Int) \cdot ((-1):Int)^{(\operatorname{Nat}.\operatorname{div}\left((\operatorname{Nat}.\operatorname{factorization}\left(n, p\right)) + 1, 2\right))})\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.C` (`✓ std3`).

*Citation.* Antti Karttunen; Sequence Machine (2024). *OEIS A369255, two Dirichlet convolution conjectures*. URL: <https://oeis.org/A369255/internal>.

*Commentary.*

OEIS A355837, revision 25, FORMULA (unpaginated). “Multiplicative with a(p^e) = 2 * (e mod 2) * (-1)^((e+1)/2) for prime p and e>0.” The empty product gives C(1) = 1. Nat.div gives the integer exponent on odd e. On even positive e the remainder factor is zero.

**Definition 1.5 (The inverse Möbius transform).**

$$\forall n \in Nat,\; \operatorname{H}\left(n\right) = \operatorname{Finset}.\operatorname{sum}\left((\operatorname{Nat}.\operatorname{divisors}\left(n\right)), (fun (d:Nat) \mapsto \operatorname{g}\left(d\right))\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.H` (`✓ std3`).

*Citation.* Antti Karttunen; Sequence Machine (2024). *OEIS A369255, two Dirichlet convolution conjectures*. URL: <https://oeis.org/A369255/internal>.

*Commentary.*

OEIS A140773, revision 51, FORMULA (unpaginated). “a(n) = Sum_{m|n} A038548(m) = Sum_{m|n} ceiling(d(m)/2), where d(m) = number of divisors of m (A000005). - _Manfred Boergens_, Feb 25 2021” Here g counts the divisors up to the square root and H sums this count over all positive divisors.

**Definition 1.6 (Both positive-index conjectures).**

$$claim = (\forall n \in Nat,\; (1 \le n) \Rightarrow ((((\operatorname{Nat}.\operatorname{mod}\left((\operatorname{H}\left(n\right)), 2\right)):Int) = \operatorname{Finset}.\operatorname{sum}\left((\operatorname{Nat}.\operatorname{divisors}\left(n\right)), (fun (d:Nat) \mapsto (\operatorname{A}\left(d\right):Int) \cdot \operatorname{B}\left((\operatorname{Nat}.\operatorname{div}\left(n, d\right))\right))\right)) \land (((\operatorname{Nat}.\operatorname{mod}\left((\operatorname{H}\left(n\right)), 2\right)):Int) = \operatorname{Finset}.\operatorname{sum}\left((\operatorname{Nat}.\operatorname{divisors}\left(n\right)), (fun (d:Nat) \mapsto (\operatorname{H}\left(d\right):Int) \cdot \operatorname{C}\left((\operatorname{Nat}.\operatorname{div}\left(n, d\right))\right))\right))))$$

*Formalization.* `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.claim` (`✓ std3`).

*Citation.* Antti Karttunen; Sequence Machine (2024). *OEIS A369255, two Dirichlet convolution conjectures*. URL: <https://oeis.org/A369255/internal>.

*Commentary.*

OEIS A369255, revision 15, FORMULA block (unpaginated). “Following convolution formulas have been conjectured for this sequence by Sequence Machine, with both computing the first 2^20 terms correctly:” “a(n) = Sum_{d|n} A007875(d)*A219009(n/d).” “a(n) = Sum_{d|n} A140773(d)*A355837(n/d).” OEIS A140773, revision 51, FORMULA (unpaginated). “a(n) = Sum_{m|n} A038548(m) = Sum_{m|n} ceiling(d(m)/2), where d(m) = number of divisors of m (A000005). - _Manfred Boergens_, Feb 25 2021” The offset is one. A140773 is the sum of g over positive divisors, and A369255 is its natural remainder modulo two. Both divisor sums use integer coefficients. Nat.div is natural-number division.

**Theorem 1.7 (Both identities).**

$$\forall n \in Nat,\; (1 \le n) \Rightarrow ((((\operatorname{Nat}.\operatorname{mod}\left((\operatorname{H}\left(n\right)), 2\right)):Int) = \operatorname{Finset}.\operatorname{sum}\left((\operatorname{Nat}.\operatorname{divisors}\left(n\right)), (fun (d:Nat) \mapsto (\operatorname{A}\left(d\right):Int) \cdot \operatorname{B}\left((\operatorname{Nat}.\operatorname{div}\left(n, d\right))\right))\right)) \land (((\operatorname{Nat}.\operatorname{mod}\left((\operatorname{H}\left(n\right)), 2\right)):Int) = \operatorname{Finset}.\operatorname{sum}\left((\operatorname{Nat}.\operatorname{divisors}\left(n\right)), (fun (d:Nat) \mapsto (\operatorname{H}\left(d\right):Int) \cdot \operatorname{C}\left((\operatorname{Nat}.\operatorname{div}\left(n, d\right))\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.result` (`✓ std3`). ∎

*Resolves.* `Problems/a369255-dirichlet` (proved) by `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"a369255-dirichlet","declaration_gid":"D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Antti Karttunen; Sequence Machine (2024). *OEIS A369255, two Dirichlet convolution conjectures*. URL: <https://oeis.org/A369255/internal>.

*Commentary.*

Swapping the two factors counts diagonal pairs once and off-diagonal pairs twice. The prime-power convolution identities reduce both doubled sums to the same arithmetic function, whose values are zero or two. The coefficient C(1) is one and every later coefficient is even, so convolution by C preserves the residue modulo two.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.A`
- Truth anchor: `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.B`
- Truth anchor: `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.C`
- Truth anchor: `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.H`
- Truth anchor: `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.claim`
- Truth anchor: `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.g`
- Truth anchor: `D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.result`
- Dependency: [D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution](../../Arith/Divisors/OeisA252505FourthPowerFreeConvolution.md)
- Dependency: [D5/S3/Arith/SchulteLiouvilleCubeMobius](../../Arith/SchulteLiouvilleCubeMobius.md)
- Dependency: [D5/S3/Factorization/Combinatorics/StrictDivisorChainCount](StrictDivisorChainCount.md)
