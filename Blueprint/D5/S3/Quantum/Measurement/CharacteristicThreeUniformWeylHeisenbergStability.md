# A uniformly stable minimal Weyl-Heisenberg measurement in characteristic three

## Abstract

Zhu and Wang (arXiv:2608.11850) measure the stability of a minimal Weyl-Heisenberg measurement by the smallest nonidentity eigenvalue of its projector Gram matrix, construct uniformly stable finite-field families in characteristic two and in characteristic at least five, and leave characteristic three open. For every q = 3^r the fiducial obtained by adding the basis vector at 0 to the uniform vector and normalizing has projector-Gram floor at least (1/8) q/(q + 1) on the complement of the constant vector, so eta is at least 1/8 for every r.

**Definition 1.1 (The field).**

$$\forall r : \mathbb{N}, \operatorname{F}\left(r\right) = \operatorname{GaloisField}\left(3, r\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.F` (`✓ std3`).

*Citation.* X. Zhu; Y. Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. DOI: [10.48550/arXiv.2608.11850](https://doi.org/10.48550/arXiv.2608.11850). URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

F(r) is the Galois field GF(3^r), the field F_q of the paper at p = 3; for r >= 1 it has q = 3^r elements.

**Definition 1.2 (The canonical additive character).**

$$\forall r : \mathbb{N}, \forall x : \operatorname{F}\left(r\right), \psi\left(x\right) = \operatorname{exp}\left(\frac{2 \cdot \pi \cdot i \cdot \operatorname{val}\left(\operatorname{trace}\left(\operatorname{ZMod}\left(3\right), \operatorname{F}\left(r\right), x\right)\right)}{3}\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.psi` (`✓ std3`).

*Citation.* X. Zhu; Y. Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. DOI: [10.48550/arXiv.2608.11850](https://doi.org/10.48550/arXiv.2608.11850). URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

The paper's psi(x) = exp(2 pi i Tr(x)/p) at p = 3, where Tr is the trace of F(r) over ZMod 3 and val is its representative in {0, 1, 2}.

**Definition 1.3 (The displacement operators).**

$$\forall r : \mathbb{N}, \forall a : \operatorname{F}\left(r\right), \forall b : \operatorname{F}\left(r\right), \forall x : \operatorname{F}\left(r\right), \forall y : \operatorname{F}\left(r\right), \operatorname{D}\left(a, b\right)\left(y, x\right) = \operatorname{ite}\left(y = x + a, \psi\left(b \cdot x\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.D` (`✓ std3`).

*Citation.* X. Zhu; Y. Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. DOI: [10.48550/arXiv.2608.11850](https://doi.org/10.48550/arXiv.2608.11850). URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

D_{a,b} = X_a Z_b with X_a|x> = |x + a> and Z_b|x> = psi(b x)|x>: the entry in row y and column x is psi(b x) when y = x + a and 0 otherwise. Here ite(c, u, v) is u if c holds and v otherwise.

**Definition 1.4 (The orbit projectors).**

$$\forall r : \mathbb{N}, \forall \varphi : \operatorname{F}\left(r\right) \to \mathbb{C}, \forall a : \operatorname{F}\left(r\right), \forall b : \operatorname{F}\left(r\right), \operatorname{proj}\left(\varphi, (a, b)\right) = \operatorname{D}\left(a, b\right) \cdot \operatorname{vecMulVec}\left(\varphi, \operatorname{star}\left(\varphi\right)\right) \cdot \operatorname{D}\left(a, b\right)^{H}$$

*Formalization.* `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.proj` (`✓ std3`).

*Citation.* X. Zhu; Y. Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. DOI: [10.48550/arXiv.2608.11850](https://doi.org/10.48550/arXiv.2608.11850). URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

Pi_{a,b} = D_{a,b} |phi><phi| D_{a,b}^dagger for g = (a, b), where vecMulVec(phi, star(phi)) is the outer product |phi><phi| and the superscript H is the conjugate transpose.

**Definition 1.5 (The projector Gram matrix).**

$$\forall r : \mathbb{N}, \forall \varphi : \operatorname{F}\left(r\right) \to \mathbb{C}, \forall u : \operatorname{F}\left(r\right) \times \operatorname{F}\left(r\right), \forall v : \operatorname{F}\left(r\right) \times \operatorname{F}\left(r\right), \operatorname{gram}\left(\varphi\right)\left(u, v\right) = \operatorname{trace}\left(\operatorname{proj}\left(\varphi, u\right) \cdot \operatorname{proj}\left(\varphi, v\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.gram` (`✓ std3`).

*Citation.* X. Zhu; Y. Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. DOI: [10.48550/arXiv.2608.11850](https://doi.org/10.48550/arXiv.2608.11850). URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

The q^2 x q^2 matrix with entries Tr(Pi_u Pi_v), indexed by pairs u, v in F(r) x F(r).

**Definition 1.6 (A lower bound for the nonidentity floor).**

$$\forall r : \mathbb{N}, \forall \varphi : \operatorname{F}\left(r\right) \to \mathbb{C}, \forall c : \mathbb{R}, \operatorname{StableWith}\left(\varphi, c\right) \Leftrightarrow (\forall w : (\operatorname{F}\left(r\right) \times \operatorname{F}\left(r\right)) \to \mathbb{C}, (\sum_{g} w\left(g\right) = 0) \Rightarrow (c \cdot \sum_{g} \Vert w\left(g\right)\Vert^{2} \le \operatorname{Re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(w\right), \operatorname{mulVec}\left(\operatorname{gram}\left(\varphi\right), w\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.StableWith` (`✓ std3`).

*Citation.* X. Zhu; Y. Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. DOI: [10.48550/arXiv.2608.11850](https://doi.org/10.48550/arXiv.2608.11850). URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

StableWith(phi, c) says that the Hermitian form of the projector Gram matrix is at least c times the squared norm on every vector w whose entries sum to zero, the orthogonal complement of the constant vector. This is the Rayleigh-quotient form of lambda(phi) >= c for the smallest nonidentity eigenvalue lambda(phi).

**Definition 1.7 (Uniform stability in characteristic three).**

$$claim \Leftrightarrow (\exists c : \mathbb{R}, (0 < c) \land (\forall r : \mathbb{N}, (1 \le r) \Rightarrow (\exists \varphi : \operatorname{F}\left(r\right) \to \mathbb{C}, (\sum_{x} \Vert \varphi\left(x\right)\Vert^{2} = 1) \land (\operatorname{StableWith}\left(\varphi, \frac{c \cdot 3^{r}}{3^{r} + 1}\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.claim` (`✓ std3`).

*Citation.* X. Zhu; Y. Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. DOI: [10.48550/arXiv.2608.11850](https://doi.org/10.48550/arXiv.2608.11850). URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

A constant c > 0 and, for every r >= 1, a unit vector phi in C^{F(r)} with lambda(phi) >= c q/(q + 1), q = 3^r; equivalently eta(phi) = ((q + 1)/q) lambda(phi) >= c for every r, the uniform spectral stability of the paper in characteristic three.

**Theorem 1.8 (Characteristic three has a uniformly stable family).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhu-wang-2026-characteristic-three-uniform-stability` (proved) by `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhu-wang-2026-characteristic-three-uniform-stability","declaration_gid":"D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* X. Zhu; Y. Wang (2026). *Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark*. DOI: [10.48550/arXiv.2608.11850](https://doi.org/10.48550/arXiv.2608.11850). URL: <https://arxiv.org/abs/2608.11850v1>.

*Commentary.*

Take c = 1/8, s = sqrt(q) and phi = (u + e_0)/sqrt(2 + 2/s) with u the normalized uniform vector. The ambiguity function A(a, b) = <phi, D_{a,b} phi> equals (delta_{b,0} + delta_{a,0} + (1 + psi(-a b))/s)/(2 + 2/s), because the character sums of psi over F(r) vanish at every nonzero frequency (the trace is a nonzero functional). Off the axes psi takes only the cube roots of unity, so |1 + psi| >= 1, and on the axes |A| = (s + 2)/(2(s + 1)); hence |A(h)|^2 >= 1/(4(s + 1)^2) for every h != 0. Expanding |phi><phi| in the orthogonal displacement basis and using the multiplication law of the displacements, the Gram form of w is (1/q) sum_h |A(h)|^2 |w^(h)|^2, where w^ is the symplectic Fourier transform of w; Parseval gives sum_h |w^(h)|^2 = q^2 sum_g |w(g)|^2, and w^(0) = sum_g w(g) = 0. So the form is at least q/(4(s + 1)^2) times the squared norm, and q/(4(s + 1)^2) >= (1/8) q/(q + 1) because 2(q + 1) - (s + 1)^2 = (s - 1)^2 >= 0.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.D`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.F`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.StableWith`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.gram`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.proj`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.psi`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeUniformWeylHeisenbergStability.result`
