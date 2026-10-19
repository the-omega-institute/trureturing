# A counterexample to the radial convexity characterization

## Abstract

Radial convexity with respect to the Frobenius norm does not imply matrix monotonicity of the same degree: an explicit rational function separates the two properties in degree three.

M. M. Czerwińska, J. A. Franco and A. Merino, Towards a Characterization of Matrix Monotonicity via Radial Convexity. arXiv:2610.17393v1, §4, Conjecture 4.10.

Conjecture 4.10. Let f : (0, ∞) → R. Then f is radially convex of order n (with respect to the Frobenius norm) if and only if f is matrix monotone of degree n.

arXiv:2610.17393v1, §4, directly after Conjecture 4.10, verbatim: “By Proposition 3.9, matrix monotonicity of degree n implies radial convexity of order n. Thus, it remains to prove the converse implication. The next theorem establishes the conjecture for n = 2.”

arXiv:2610.17393v1, §1, verbatim: “In degree 3, we show that radial convexity already provides the principal minor conditions required for matrix monotonicity, leaving the sign of the determinant of the Loewner matrix as the remaining obstruction.”

**Definition 1.1 (Conjecture 4.10 with its universal quantifiers).**

Lean statement: `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.conjecture`

*Formalization.* `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.conjecture` (`✓ std3`).

*Citation.* M. M. Czerwińska; J. A. Franco; A. Merino (2026). *Towards a Characterization of Matrix Monotonicity via Radial Convexity*. DOI: [10.48550/arXiv.2610.17393](https://doi.org/10.48550/arXiv.2610.17393). URL: <https://arxiv.org/abs/2610.17393>.

*Commentary.*

For each natural n≥1 and each real scalar function, the conjecture equates the two Frobenius endpoint inequalities on all ordered positive definite complex Hermitian triples with either uniformly increasing or uniformly decreasing Loewner monotonicity on all positive definite pairs. The function is represented on the real line; the positive-definite spectrum restricts its relevant values to (0,∞).

**Theorem 1.2 (Opposite signs on an ordered positive pair).**

Lean statement: `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.finite_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both endpoints are positive definite and A≤B. Their difference is (2/75)ww* for w=(2,3,6). The increment has quadratic form −2/111549375 at v=(−35,48,−15) and a strictly positive (0,0) entry. Its six inverses are verified by exact matrix multiplication. This excludes both monotonicity directions on the same pair.

**Theorem 1.3 (Neither direction of matrix monotonicity).**

Lean statement: `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.not_matrix_monotone`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.not_matrix_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuous functional calculus identifies the scalar and matrix rational expressions. The finite certificate contradicts positivity in the increasing direction and diagonal positivity in the decreasing direction, as allowed by Definition 2.15.

**Theorem 1.4 (Conjecture 4.10 is false in degree three).**

Lean statement: `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.result` (`✓ std3`). ∎

*Resolves.* `Problems/czerwinska-franco-merino-2026-radial-convexity-matrix-monotonicity` (refuted) by `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"czerwinska-franco-merino-2026-radial-convexity-matrix-monotonicity","declaration_gid":"D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. M. Czerwińska; J. A. Franco; A. Merino (2026). *Towards a Characterization of Matrix Monotonicity via Radial Convexity*. DOI: [10.48550/arXiv.2610.17393](https://doi.org/10.48550/arXiv.2610.17393). URL: <https://arxiv.org/abs/2610.17393>.

*Commentary.*

Take ε=1/20000 and f(t)=(t+1)/(t+3)+(t+1)/(2t+4)−ε(t+1)/(3t+5). The Cayley map h(A)=I−2(A+I)⁻¹ is order preserving from the positive cone into −I<X<I, and continuous functional calculus identifies f(A) with g(h(A)), where g(X)=R_2(X)+R_3(X)−εR_4(X).

Uniform endpoint resolvent factors and three-node spectral interpolation give positivity of Dg_C(g(V)−g(U)) at both endpoints C=U,V. The positive remainder coefficient is 1/3−324ε=4757/15000. The actual derivative and Frobenius trace pairing then make the squared endpoint distances monotone along ordered segments. Thus the full order-three radial property holds for every positive definite triple.

For A=diag(1/3,1,3) and B=(1/25)[[11,4,8],[4,31,12],[8,12,99]], the difference B−A=(2/75)ww* with w=(2,3,6). At v=(−35,48,−15), the exact quadratic form v*(f(B)−f(A))v is −2/111549375, while the (0,0) entry of f(B)−f(A) is positive. Both possible matrix-monotonicity directions therefore fail.

The paper's order-two differentiable theorem is unaffected. Direct sums extend the finite nonmonotonicity certificate to higher dimensions, but do not supply the all-matrix radial property there. A characterization of radial convexity and refutations in every higher dimension remain separate questions.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.conjecture`
- Truth anchor: `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.finite_certificate`
- Truth anchor: `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.not_matrix_monotone`
- Truth anchor: `D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample.result`
- Dependency: [D5/S3/Quantum/Matrix/CfmEndpointPositivity](CfmEndpointPositivity.md)
- Dependency: [D5/S3/Quantum/Matrix/CfmMonotonicityCertificate](CfmMonotonicityCertificate.md)
