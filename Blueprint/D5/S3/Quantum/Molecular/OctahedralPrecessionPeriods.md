# Octahedral precession periods modulo 3

## Abstract

The coefficients a(n) of OEIS A318245, the scaled period of the precession of the angular momentum vector J along a curve of the rotational energy surface of an octahedral molecule, are integers divisible by 3 for every n at least 1, as conjectured by Bradley Klee in 2018. The proof gives the closed form a(n) = sum over k + j = n of C(2k,k) C(2j,j) C(2k+j,k) 4^j and shows that it is multiplicative in the base-3 digits of n modulo 3.

**Definition 1.1 (The sequence A318245).**

$$\left(\operatorname{a}\left(0\right) = 1 \land \operatorname{a}\left(1\right) = 12\right) \land \left(\forall n \in \mathbb{N},\; \operatorname{a}\left(n + 2\right) = \frac{4 \cdot (28 \cdot \left(n + 2\right)^{2} - 28 \cdot \left(n + 2\right) + 9) \cdot \operatorname{a}\left(n + 1\right) - 64 \cdot (4 \cdot \left(n + 2\right) - 5) \cdot (4 \cdot \left(n + 2\right) - 3) \cdot \operatorname{a}\left(n\right)}{3 \cdot \left(n + 2\right)^{2}}\right)$$

*Formalization.* `D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.a` (`✓ std3`).

*Citation.* Bradley Klee (2018). *OEIS A318245, scaled period of J-vector precession for octahedral molecules: the conjecture a(n) mod 3 = 0*. URL: <https://oeis.org/A318245>.

*Commentary.*

The scaled generating function T(v) = sum of a(n) (3v/64)^n satisfies 9(5v - 4)T + d/dv(16v(v - 1)(3v - 4)T') = 0 with a(0) = 1. Comparing the coefficients of v^n gives a(1) = 12 from the constant term and the three-term recurrence of the entry for every n at least 2; the sequence is defined over the rationals, where the recurrence divides by 3n^2.

**Definition 1.2 (Klee's conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 0 < n \Rightarrow (\exists z \in \mathbb{Z},\; \operatorname{a}\left(n\right) = 3 \cdot z))$$

*Formalization.* `D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.claim` (`✓ std3`).

*Citation.* Bradley Klee (2018). *OEIS A318245, scaled period of J-vector precession for octahedral molecules: the conjecture a(n) mod 3 = 0*. URL: <https://oeis.org/A318245>.

*Commentary.*

For every n at least 1, a(n) is three times an integer: a(n) is an integer and a(n) mod 3 = 0.

**Theorem 1.3 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a318245-klee-octahedral-mod3` (proved) by `D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a318245-klee-octahedral-mod3","declaration_gid":"D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Bradley Klee (2018). *OEIS A318245, scaled period of J-vector precession for octahedral molecules: the conjecture a(n) mod 3 = 0*. URL: <https://oeis.org/A318245>.

*Commentary.*

Let t(k, j) = C(2k,k) C(2j,j) C(2k+j,k) 4^j and b(n) = sum of t(k, j) over k + j = n. Two ratio identities hold in the natural numbers: t(k, j+1)(j+1)(k+j+1) = 8 t(k, j)(2j+1)(2k+j+1) and 4 t(k+1, j)(k+1)^2(2j+1) = t(k, j+1)(2k+1)(j+1)(2k+j+2). Put n = N + 2 and G(k) = t(k, n-k) R(k) with R(k) = 2k^2 n(4kn - 4n^2 + 6n - 3)/((n+k)(n+k-1)(2n-2k-1)). By the ratio identities, 3n^2 t(k, j+2) - 4(28n^2 - 28n + 9) t(k, j+1) + 64(4n-5)(4n-3) t(k, j) = G(k+1) - G(k) for k + j = N, and the two boundary terms k = N+1, N+2 cancel against G(N+1); since G(0) = 0 the sum telescopes, so b satisfies the recurrence of the entry. As b(0) = 1 and b(1) = 12, induction gives a(n) = b(n). By Lucas' theorem at the prime 3, C(2k,k) with k = 3i + s is congruent to C(2s,s) C(2i,i), and C(2k+j,k) splits in the same way with a carry that only occurs when a factor C(2s,s) C(2e,e) C(2s+e,s) with 2s + e at least 3 already vanishes modulo 3; as 4 is congruent to 1, t(3i+s, 3a+e) is congruent to t(s, e) t(i, a) for s, e less than 3. Splitting each k in the sum for b(3m + r) into its last base-3 digit, the terms whose last digits carry vanish and the rest regroup to b(3m + r) congruent to b(r) b(m) modulo 3. Since b(1) = 12 and b(2) = 180 are divisible by 3 and b(0) = 1, strong induction on n gives that 3 divides b(n) for every n at least 1.

## References

- Truth anchor: `D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.a`
- Truth anchor: `D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.claim`
- Truth anchor: `D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.result`
