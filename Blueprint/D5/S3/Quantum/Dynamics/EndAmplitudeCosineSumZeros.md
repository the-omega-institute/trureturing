# Zeros of the end amplitude numerator of a seven-site chain

## Abstract

For natural numbers a < b < c with a and c odd, b even and gcd(a, b, c) = 1, the cosine sum N(t) = (b^2 - a^2)(c^2 - a^2)(c^2 - b^2) + b^2 c^2 (c^2 - b^2) cos(at) + a^2 c^2 (c^2 - a^2) cos(bt) + a^2 b^2 (b^2 - a^2) cos(ct) has a zero in the open interval (0, pi) if and only if a is not 1. For a = 1 it is positive on [0, pi); for a >= 3 it takes a negative value in (0, pi).

**Definition 1.1 (The amplitude numerator).**

$$\operatorname{amplitudeNumerator}\left(a, b, c, t\right) = \left(b^{2} - a^{2}\right) \cdot \left(c^{2} - a^{2}\right) \cdot \left(c^{2} - b^{2}\right) + b^{2} \cdot c^{2} \cdot \left(c^{2} - b^{2}\right) \cdot \operatorname{cos}\left(a \cdot t\right) + a^{2} \cdot c^{2} \cdot \left(c^{2} - a^{2}\right) \cdot \operatorname{cos}\left(b \cdot t\right) + a^{2} \cdot b^{2} \cdot \left(b^{2} - a^{2}\right) \cdot \operatorname{cos}\left(c \cdot t\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator` (`✓ std3`).

*Citation.* Mia Gabriella Escobar; Valentin Garcia; Anastasiia Minenkova (2025). *Early State Exclusion in 7-Qubit Spin Chains*. DOI: [10.48550/arXiv.2507.18767](https://doi.org/10.48550/arXiv.2507.18767). URL: <https://arxiv.org/abs/2507.18767v1>.

*Commentary.*

The cosine sum N(a, b, c; t) attached to the seven frequencies 0, a, -a, b, -b, c, -c. For a chain of seven sites whose spectrum is a positive multiple of {0, a, -a, b, -b, c, -c}, with first-site spectral weights proportional to the reciprocals of the products of the gaps to the other frequencies, the first-site amplitude is a positive multiple of N at a rescaled time: clearing the denominators of 1/(a^2 b^2 c^2) + cos(at)/(a^2 (b^2 - a^2)(c^2 - a^2)) + cos(bt)/(b^2 (b^2 - a^2)(c^2 - b^2)) + cos(ct)/(c^2 (c^2 - a^2)(c^2 - b^2)) gives N. N is the bracket of Eq. (2.1) of Escobar, Garcia and Minenkova, arXiv:2507.18767, read at natural frequencies (x, y, z) = (a, b, c): that equation gives the first-site amplitude of the persymmetric seven-site chain with spectrum {0, x, -x, y, -y, z, -z} as the bracket divided by 2 y^2 (z^2 - x^2)(x^2 - y^2 + z^2). This module treats N as a function in its own right and does not formalise the chain.

**Theorem 1.2 (Positivity for a = 1).**

$$\forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; (\operatorname{Even}\left(b\right) \land \operatorname{Odd}\left(c\right) \land 1 < b \land b < c) \Rightarrow (\forall t \in \mathbb{R},\; (0 \le t \land t < \pi) \Rightarrow (0 < \operatorname{amplitudeNumerator}\left(1, b, c, t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mia Gabriella Escobar; Valentin Garcia; Anastasiia Minenkova (2025). *Early State Exclusion in 7-Qubit Spin Chains*. DOI: [10.48550/arXiv.2507.18767](https://doi.org/10.48550/arXiv.2507.18767). URL: <https://arxiv.org/abs/2507.18767v1>.

*Commentary.*

Put t = pi - 2 theta with theta in (0, pi/2]. Since cos(k (pi - 2 theta)) = (-1)^k (1 - 2 sin^2(k theta)) and the constant term of N equals C1 - C2 + C3 with C1 = b^2 c^2 (c^2 - b^2), C2 = a^2 c^2 (c^2 - a^2), C3 = a^2 b^2 (b^2 - a^2), the parities of a, b, c give N(pi - 2 theta) = 2 B(theta), B = C1 sin^2(a theta) - C2 sin^2(b theta) + C3 sin^2(c theta). For a = 1, writing psi(x) = (sin x / x)^2, u = b theta, v = c theta and sin^2(k theta) = (k theta)^2 psi(k theta), one finds B = b^2 c^2 ((psi(theta) - psi(u))(v^2 - theta^2) - (psi(theta) - psi(v))(u^2 - theta^2)), which is positive because the chord slope of psi in the squared variable from the base point theta in (0, pi/2] is strictly decreasing and theta < u < v. The source proves the case (b, c) = (2m, 2m + 1), its Theorem 3.2, by a different argument; the statement for every even b and odd c with 1 < b < c is derived here.`D5/S3/Quantum/Dynamics/SincSquareChordSlope.sincSq_chord_lt`

**Theorem 1.3 (A negative value for a >= 3).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; (\operatorname{Odd}\left(a\right) \land \operatorname{Even}\left(b\right) \land \operatorname{Odd}\left(c\right) \land 3 \le a \land a < b \land b < c \land \operatorname{gcd}\left(\operatorname{gcd}\left(a, b\right), c\right) = 1) \Rightarrow (\exists t \in \mathbb{R},\; 0 < t \land t < \pi \land \operatorname{amplitudeNumerator}\left(a, b, c, t\right) < 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.exists_amplitudeNumerator_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mia Gabriella Escobar; Valentin Garcia; Anastasiia Minenkova (2025). *Early State Exclusion in 7-Qubit Spin Chains*. DOI: [10.48550/arXiv.2507.18767](https://doi.org/10.48550/arXiv.2507.18767). URL: <https://arxiv.org/abs/2507.18767v1>.

*Commentary.*

The numerator is even in t, so it suffices to find theta in (0, pi), theta different from pi/2, with B(theta) < 0 in the notation of the previous statement; the time is |pi - 2 theta|. Note C2 > C3 > 0. If a does not divide b, take theta = pi j / a with 0 < j < a, which is never pi/2 because a is odd: then sin(a theta) = 0 and B = -C2 s_b(j) + C3 s_c(j) with s_m(j) = sin^2(pi j m / a). For m not divisible by a the sum of s_m(j) over the a residues j is a/2, by the closed form of the sum of cos(2 pi j m / a), and for m divisible by a every s_m(j) vanishes; so the sum of s_b is a/2 and the sum of s_c is at most a/2. Hence some residue j has s_b(j) > 0 and s_c(j) <= s_b(j) (otherwise s_b <= s_c termwise with strict inequality at j = 1); necessarily j is not 0, and B <= -(C2 - C3) s_b(j) < 0. If a divides b, write b = a beta with beta >= 2; then a does not divide c because gcd(a, b, c) = 1 and a >= 3, so d = gcd(a, c) is a proper divisor of the odd number a, whence 3d <= a and d < c. Choose 0 < l < c with a l congruent to d modulo c and take theta = pi l / c, which is not pi/2 because c is odd. Then sin(c theta) = 0, sin^2(a theta) = sin^2 x and sin^2(b theta) = sin^2(beta x) with x = pi d / c, and B = a^2 c^2 (beta^2 (c^2 - b^2) sin^2 x - (c^2 - a^2) sin^2(beta x)). Put y = beta x; then 0 < y < pi/3 because 3 beta d <= b < c. From sin y > y - y^3/6 > 0 and 0 < sin x < x one gets sin^2 y > y^2 (1 - y^2/3) >= beta^2 sin^2 x (1 - y^2/3), and (c^2 - a^2)(1 - y^2/3) - (c^2 - b^2) = (b^2 - a^2) - (c^2 - a^2) y^2/3 >= 0 since (c^2 - a^2) y^2/3 <= pi^2 beta^2 d^2/3 <= 16 beta^2 a^2/27 <= (beta^2 - 1) a^2 for beta >= 2. Hence B < 0. The source's Theorem 3.4 treats the triples (a, b, c) = (2m + 1, 2m + 2, 2m + 3) and finds exactly 2m zeros of N in (0, pi) for them; a negative value for every admissible triple with a >= 3 is derived here, and the number of zeros is not addressed.

**Theorem 1.4 (The numerator vanishes in (0, pi) exactly when a is not 1).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall c \in \mathbb{N},\; (\operatorname{Odd}\left(a\right) \land \operatorname{Even}\left(b\right) \land \operatorname{Odd}\left(c\right) \land a < b \land b < c \land \operatorname{gcd}\left(\operatorname{gcd}\left(a, b\right), c\right) = 1) \Rightarrow ((\exists t \in \mathbb{R},\; 0 < t \land t < \pi \land \operatorname{amplitudeNumerator}\left(a, b, c, t\right) = 0) \Leftrightarrow (a \ne 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mia Gabriella Escobar; Valentin Garcia; Anastasiia Minenkova (2025). *Early State Exclusion in 7-Qubit Spin Chains*. DOI: [10.48550/arXiv.2507.18767](https://doi.org/10.48550/arXiv.2507.18767). URL: <https://arxiv.org/abs/2507.18767v1>.

*Commentary.*

The numerator is continuous and N(0) > 0, all four terms being positive at t = 0. If a is not 1 then a >= 3 because a is odd, the previous statement gives a time t1 in (0, pi) with N(t1) < 0, and the intermediate value theorem gives a zero in (0, t1). If a = 1 then b > 1 and the positivity statement excludes zeros in (0, pi). For a seven-site chain with perfect state transfer at its earliest time and symmetric spectrum, the condition a = 1 says that every positive eigenvalue is an integer multiple of the smallest one, and a zero of N in (0, pi) is a time before the transfer time at which the first-site amplitude vanishes; this is the cosine-sum form of the conjecture of Section 4 of the source. The source proves the families of its Theorems 3.2 and 3.4 and states the general case as a conjecture; the equivalence for every admissible triple is derived here. The statement is about the function N only, and the reduction of the chain to N is not part of this module.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator`
- Truth anchor: `D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator_pos`
- Truth anchor: `D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator_zero_iff`
- Truth anchor: `D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.exists_amplitudeNumerator_neg`
- Truth anchor: `D5/S3/Quantum/Dynamics/SincSquareChordSlope.sincSq_chord_lt`
- Dependency: [D5/S3/Quantum/Dynamics/SincSquareChordSlope](SincSquareChordSlope.md)
