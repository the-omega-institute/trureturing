# No perfect state transfer at time pi on rational paths with 2m vertices, m = 2 mod 4 or m = 3, 5 mod 8

## Abstract

Kirkland, McLaren, Pereira, Plosker and Zhang (arXiv:1708.03283) conjecture that a weighted path on at least four vertices, with or without potentials, whose edge weights are all rational has no perfect state transfer between its end vertices at readout time pi, and prove it for n = 4 and for n congruent to 3 or 5 modulo 8. The statement holds for every even number of vertices n = 2m with m congruent to 2 modulo 4 or to 3 or 5 modulo 8, that is for n congruent to 4 modulo 8 or to 6 or 10 modulo 16, with arbitrary real potentials and in both directions. The conjecture is not settled for n congruent to 0 modulo 8 or to 2 or 14 modulo 16.

**Theorem 1.1 (Residue modulo 4 of the second Hankel determinant of the nodal moments).**

$$\forall iota \in Type,\; \forall z \in iota \to \mathbb{Z},\; \forall A \in \operatorname{Finset}\left(iota\right),\; \forall B \in \operatorname{Finset}\left(iota\right),\; \forall k \in \mathbb{N},\; \operatorname{card}\left(A\right) = k + 1 \Rightarrow (\operatorname{card}\left(B\right) = k + 1 \Rightarrow ((\forall l \in A,\; \operatorname{Even}\left(z\left(l\right)\right)) \Rightarrow ((\forall l \in B,\; \operatorname{Odd}\left(z\left(l\right)\right)) \Rightarrow (((k + 1) \bmod 4 = 2 \lor \left((k + 1) \bmod 8 = 3 \lor (k + 1) \bmod 8 = 5\right)) \Rightarrow (((\operatorname{nodalMoment}\left(z, A, B, k, 0\right) \cdot \operatorname{nodalMoment}\left(z, A, B, k, 2\right) - \operatorname{nodalMoment}\left(z, A, B, k, 1\right)^{2} : \mathbb{Z}) : \operatorname{ZMod}\left(4\right)) = \operatorname{ite}\left((k + 1) \bmod 4 = 2, 3, 2\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer.nodalMoment_det_mod_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

Let C p be the nodal moment of order p and degree k of A against B, the coefficient of X^k in the remainder of X^p P_B modulo P_A, for the monic polynomials P_A and P_B whose roots are the k + 1 even integers z l, l in A, and the k + 1 odd integers z l, l in B. Modulo 4 a product of k + 1 factors y + 2 e_l equals y^k (y + 2 sum_l e_l), because 2 * 2 = 0; hence P_A reduces to X^k (X + c) and P_B to (X + 1)^k (X + 1 + d) with c and d even residues, so that c^2 = d^2 = 0. Since (X - c) X^k (X + c) = X^(k+2), the coefficient of X^k in the remainder of a polynomial g modulo X^k (X + c) is the coefficient of X^(k+1) in (X - c) g. For g = X^p (X + 1)^k (X + 1 + d) and p <= k + 1 this is the coefficient of X^(p+1) in the reflected polynomial (1 - c X)(1 + X)^k (1 + X + d X), the factor (X + 1)^k being palindromic. Therefore, modulo 4, C 0 = k + (1 + d - c), C 1 = C(k, 2) + (1 + d - c) k - c (1 + d) and C 2 = C(k, 3) + (1 + d - c) C(k, 2) - c (1 + d) k. By the Vandermonde identity and the divisibility of C(8, i) by 4 for 1 <= i <= 3, the binomial coefficients C(k, j) with j <= 3 depend modulo 4 only on k modulo 8. The hypothesis on k + 1 says that k is congruent to 1, 5, 2 or 4 modulo 8, and evaluating the three expressions for the residues c, d with c^2 = d^2 = 0 in each of the four cases gives C 0 C 2 - (C 1)^2 = 3 when k + 1 is congruent to 2 modulo 4 and C 0 C 2 - (C 1)^2 = 2 when k + 1 is congruent to 3 or 5 modulo 8. In the formal statement the congruence is the equality of the image of the integer C 0 C 2 - (C 1)^2 in the integers modulo 4 with the conditional value 3 or 2, mod is the remainder of the division of natural numbers, and A and B are arbitrary finite sets of indices with the stated sizes and parities. For n = 4 the source shows that an explicit integer attached to the weight next to the middle edge is congruent to 3 or 7 modulo 8; the residues for general k are derived here.

**Definition 1.2 (The rational weights statement on 2m vertices, m = 2 mod 4 or m = 3, 5 mod 8).**

$$claim \Leftrightarrow (\forall m \in \mathbb{N},\; 2 \le m \Rightarrow ((m \bmod 4 = 2 \lor \left(m \bmod 8 = 3 \lor m \bmod 8 = 5\right)) \Rightarrow (\forall r \in \operatorname{Fin}\left(2 \cdot m - 1\right) \to \mathbb{R},\; \forall q \in \operatorname{Fin}\left(2 \cdot m - 1 + 1\right) \to \mathbb{R},\; (\forall j \in \operatorname{Fin}\left(2 \cdot m - 1\right),\; \exists x \in \mathbb{Q},\; r\left(j\right) = x) \Rightarrow ((\forall j \in \operatorname{Fin}\left(2 \cdot m - 1\right),\; 0 < r\left(j\right)) \Rightarrow (\left(\neg \operatorname{HasPST}\left(\operatorname{pathHamiltonian}\left(r, q\right), \pi, 0, \operatorname{last}\left(2 \cdot m - 1\right)\right)\right) \land \left(\neg \operatorname{HasPST}\left(\operatorname{pathHamiltonian}\left(r, q\right), \pi, \operatorname{last}\left(2 \cdot m - 1\right), 0\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

For m >= 2 with m congruent to 2 modulo 4 or to 3 or 5 modulo 8, and the path on n = 2m vertices with edge weights r in Fin(2m - 1) -> R and potentials q in Fin(2m - 1 + 1) -> R: if every weight is rational and positive, there is no perfect state transfer at time pi from the first vertex 0 to the last vertex 2m - 1, nor from the last vertex to the first. The rationality hypothesis is written as the existence of a rational number equal to each weight, and mod is the remainder of the division of natural numbers. The source states its conjecture for all n >= 4; the statement is the restriction of that conjecture to the sizes n = 2m with m in these residue classes.

**Theorem 1.3 (Rational paths with 2m vertices, m = 2 mod 4 or m = 3, 5 mod 8, have no transfer at time pi).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

By the reduction of end-to-end transfer to phase one, it suffices to show that for every choice of the potentials the entry of exp(i pi H) at the last and first vertices is not 1: the propagator is symmetric, and an entry gamma = exp(i pi theta) of modulus one becomes 1 after subtracting theta from every potential. Write m = k + 1 and suppose that this entry is 1. Then H is invariant under the reversal of the vertices. Let rho be the weight of the middle edge, r' the weight of the edge following it, and S p the moment of H^p at the sum of the two middle basis vectors. The numbers C p = rho S p are the integer nodal moments of the even spectral class against the odd one, each of k + 1 eigenvalues, and by the Gram identity C 0 C 2 - (C 1)^2 = rho^2 (S 0 S 2 - (S 1)^2) = (2 rho r')^2. If rho and r' are rational, this integer is the square of a rational number, hence the square of an integer, hence congruent to 0 or 1 modulo 4. But it is congruent to 3 modulo 4 when m is congruent to 2 modulo 4 and to 2 modulo 4 when m is congruent to 3 or 5 modulo 8. Only the rationality of the middle weight and of the weight next to it is used. The source proves the conjecture for n = 4 and for n congruent to 3 or 5 modulo 8, and for n = 4 it does so by showing that the weight next to the middle edge is irrational; m = 2 is that case. This is partial progress on the conjecture of the source: beyond n = 4 the sizes covered are n = 12, 20, 28, ... and n = 6, 10, 22, 26, ...; the sizes n congruent to 0 modulo 8 and to 2 or 14 modulo 16 are not addressed.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer.nodalMoment_det_mod_four`
- Truth anchor: `D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer.result`
- Dependency: [D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer](OddPathRationalWeightTransfer.md)
- Dependency: [D5/S3/Quantum/Dynamics/PathMiddleEdgeMoments](PathMiddleEdgeMoments.md)
