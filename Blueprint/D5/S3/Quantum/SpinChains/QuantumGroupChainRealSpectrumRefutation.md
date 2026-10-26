# A counterexample to real spectra with positive couplings

## Abstract

A positive-coupling quantum-group spin chain has a nonreal eigenvalue.

**Definition 1.1 (Tensor-basis digits).**

$$\forall (n : \mathbb{N}), \forall (N : \mathbb{N}), \forall (x : \operatorname{Fin}\left((n + 1)^{N}\right)), \forall (k : \operatorname{Fin}\left(N\right)), \operatorname{digit}\left(x, k\right) = \operatorname{fin}\left(\operatorname{mod}\left(\operatorname{div}\left(\operatorname{val}\left(x\right), (n + 1)^{N - 1 - \operatorname{val}\left(k\right)}\right), n + 1\right), n + 1\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.digit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tensor basis is indexed by base-(n+1) words of length N, with the leftmost digit first. Throughout, val(x) is the natural value of a finite index, and fin(t,d) is the element of Fin(d) with value t; its bound is supplied by the displayed domains. div and mod are natural-number division and remainder, and subtraction between natural numbers is truncated. cast(A,B,t) denotes the canonical coercion of t from A to B, including every real-to-complex and natural-to-real coercion in the formulas.

**Definition 1.2 (Real q-numbers).**

$$\forall (\gamma : \mathbb{R}), \forall (t : \mathbb{R}), \operatorname{qnum}\left(\gamma, t\right) = \frac{\operatorname{sin}\left(\gamma \cdot t\right)}{\operatorname{sin}\left(\gamma\right)}$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.qnum` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

The q-number [t] is sin(γt)/sin(γ). Real division is total, so this definition also has a value when sin(γ)=0. The spectral claim below restricts γ to the nonzero admissible range.

**Definition 1.3 (The deformation parameter).**

$$\forall (\gamma : \mathbb{R}), \operatorname{q}\left(\gamma\right) = \operatorname{cast}\left(\mathbb{R}, \mathbb{C}, \operatorname{cos}\left(\gamma\right)\right) + \operatorname{I} \cdot \operatorname{cast}\left(\mathbb{R}, \mathbb{C}, \operatorname{sin}\left(\gamma\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.q` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

The parameter q=exp(iγ) lies on the unit circle; I denotes the imaginary unit. The defining algebra relations are [E,F]=(K²−K⁻²)/(q−q⁻¹), KE=qEK and KF=q⁻¹FK, as in Eq. (Uq).

**Definition 1.4 (Weights in the finite basis).**

$$\forall (n : \mathbb{N}), \forall (i : \operatorname{Fin}\left(n + 1\right)), \operatorname{weight}\left(n, i\right) = \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, \operatorname{val}\left(i\right)\right) - \frac{\operatorname{cast}\left(\mathbb{N}, \mathbb{R}, n\right)}{2}$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural parameter n is twice the spin S. Basis index i has weight val(i)−n/2, so the increasing index order runs from −S to S.

**Definition 1.5 (The raising operator).**

$$\forall (n : \mathbb{N}), \forall (\gamma : \mathbb{R}), \forall (i : \operatorname{Fin}\left(n + 1\right)), \forall (j : \operatorname{Fin}\left(n + 1\right)), \operatorname{E}\left(n, \gamma\right)\left(i, j\right) = \operatorname{ite}\left((\operatorname{val}\left(i\right) = \operatorname{val}\left(j\right) + 1), \operatorname{cast}\left(\mathbb{R}, \mathbb{C}, \sqrt{\operatorname{qnum}\left(\gamma, \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, n - \operatorname{val}\left(j\right)\right)\right) \cdot \operatorname{qnum}\left(\gamma, \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, \operatorname{val}\left(j\right) + 1\right)\right)}\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.E` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

In the basis of weights −S,−S+1,…,S, the matrix entry with row i and column j raises the weight by one. Its coefficient is the square root in Eq. (EFK), with n=2S. The square root is taken in the reals before its complex coercion.

**Definition 1.6 (The lowering operator).**

$$\forall (n : \mathbb{N}), \forall (\gamma : \mathbb{R}), \forall (i : \operatorname{Fin}\left(n + 1\right)), \forall (j : \operatorname{Fin}\left(n + 1\right)), \operatorname{F}\left(n, \gamma\right)\left(i, j\right) = \operatorname{ite}\left((\operatorname{val}\left(j\right) = \operatorname{val}\left(i\right) + 1), \operatorname{cast}\left(\mathbb{R}, \mathbb{C}, \sqrt{\operatorname{qnum}\left(\gamma, \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, \operatorname{val}\left(j\right)\right)\right) \cdot \operatorname{qnum}\left(\gamma, \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, n - \operatorname{val}\left(j\right) + 1\right)\right)}\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.F` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

This is the lowering operator of Eq. (EFK), in the same increasing-weight basis. The subtraction n−val(j)+1 is performed in the naturals before coercion to the reals.

**Definition 1.7 (The diagonal weight operator).**

$$\forall (n : \mathbb{N}), \forall (\gamma : \mathbb{R}), \operatorname{K}\left(n, \gamma\right) = \operatorname{diagonal}\left((\lambda (i : \operatorname{Fin}\left(n + 1\right)), \operatorname{q}\left(\gamma \cdot \operatorname{weight}\left(n, i\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.K` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

The diagonal entry at i is exp(iγ(val(i)−n/2)), the action of K in Eq. (EFK). diagonal(f) has entries f(i) on the diagonal and zero off the diagonal.

**Definition 1.8 (The inverse weight operator).**

$$\forall (n : \mathbb{N}), \forall (\gamma : \mathbb{R}), \operatorname{Kinv}\left(n, \gamma\right) = \operatorname{diagonal}\left((\lambda (i : \operatorname{Fin}\left(n + 1\right)), \operatorname{q}\left(-(\gamma \cdot \operatorname{weight}\left(n, i\right))\right))\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.Kinv` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

The diagonal entries are exp(−iγ(val(i)−n/2)), giving the inverse of K.

**Definition 1.9 (The tensor Casimir).**

$$\forall (n : \mathbb{N}), \forall (\gamma : \mathbb{R}), \operatorname{tensorCasimir}\left(n, \gamma\right) = (\operatorname{let} de = \operatorname{tensor}\left(\operatorname{E}\left(n, \gamma\right), \operatorname{Kinv}\left(n, \gamma\right)\right) + \operatorname{tensor}\left(\operatorname{K}\left(n, \gamma\right), \operatorname{E}\left(n, \gamma\right)\right); (\operatorname{let} df = \operatorname{tensor}\left(\operatorname{F}\left(n, \gamma\right), \operatorname{Kinv}\left(n, \gamma\right)\right) + \operatorname{tensor}\left(\operatorname{K}\left(n, \gamma\right), \operatorname{F}\left(n, \gamma\right)\right); (\operatorname{let} dk = \operatorname{tensor}\left(\operatorname{K}\left(n, \gamma\right), \operatorname{K}\left(n, \gamma\right)\right); (\operatorname{let} dki = \operatorname{tensor}\left(\operatorname{Kinv}\left(n, \gamma\right), \operatorname{Kinv}\left(n, \gamma\right)\right); \operatorname{smul}\left(\frac{1}{2}, de \cdot df + df \cdot de\right) - \operatorname{smul}\left(\operatorname{cast}\left(\mathbb{R}, \mathbb{C}, \frac{\operatorname{cos}\left(\gamma\right)}{4 \cdot (\operatorname{sin}\left(\gamma\right))^{2}}\right), (dk - dki) \cdot (dk - dki)\right)))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.tensorCasimir` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

Here tensor is the Kronecker product with multiplication of complex entries. The four local expressions de, df, dk and dki are the represented coproducts Δ(E), Δ(F), Δ(K) and Δ(K⁻¹). Thus the formula is (π⊗π)Δ(C), using the coproduct of Eq. (DelEFK) and the Casimir C=(EF+FE)/2−cos(γ)(K−K⁻¹)²/(4sin²(γ)) of Eq. (C). It follows the definitional left side of Eq. (dC2). smul denotes scalar multiplication.

**Definition 1.10 (Casimir values on irreducible summands).**

$$\forall (\gamma : \mathbb{R}), \forall (l : \mathbb{N}), \operatorname{casimirValue}\left(\gamma, l\right) = \operatorname{qnum}\left(\gamma, \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, l\right)\right) \cdot \operatorname{qnum}\left(\gamma, \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, l + 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.casimirValue` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

On the spin-l irreducible summand the Casimir value is [l][l+1], as stated after Eq. (C). The successor l+1 is a natural number before coercion.

**Definition 1.11 (Products in increasing index order).**

$$\forall (\alpha : \operatorname{Type}), ([\operatorname{Monoid}\left(\alpha\right)]) \to (\forall (f : (\mathbb{N}) \to (\alpha)), (\operatorname{orderedProduct}\left(f, 0\right) = 1) \land (\forall (k : \mathbb{N}), \operatorname{orderedProduct}\left(f, k + 1\right) = \operatorname{orderedProduct}\left(f, k\right) \cdot f\left(k\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.orderedProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty product is one. Each recursive step multiplies on the right by the next factor, fixing an order even in a noncommutative monoid. Bracketed typeclass assumptions in the displays are anonymous instance arguments.

**Definition 1.12 (The Casimir spectral projector).**

$$\forall (n : \mathbb{N}), \forall (s : \mathbb{N}), \forall (\gamma : \mathbb{R}), \operatorname{projector}\left(n, s, \gamma\right) = \operatorname{orderedProduct}\left((\lambda (l : \mathbb{N}), \operatorname{ite}\left((l \ne s), \operatorname{smul}\left(\operatorname{inv}\left(\operatorname{cast}\left(\mathbb{R}, \mathbb{C}, \operatorname{qnum}\left(\gamma, \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, s\right) - \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, l\right)\right)\right) \cdot \operatorname{cast}\left(\mathbb{R}, \mathbb{C}, \operatorname{qnum}\left(\gamma, \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, s + l + 1\right)\right)\right)\right), \operatorname{tensorCasimir}\left(n, \gamma\right) - \operatorname{smul}\left(\operatorname{cast}\left(\mathbb{R}, \mathbb{C}, \operatorname{casimirValue}\left(\gamma, l\right)\right), 1\right)\right), 1\right)), n + 1\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.projector` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

With n=2S, this is P^{S,s} from Eq. (PjC). The product runs through l=0,…,n in increasing order, inserting the identity at l=s. Each other factor is (C^{S,S}−[l][l+1]I)/([s−l][s+l+1]). The denominator factors are separately coerced to the complexes before multiplication and inversion. In the spectral claim all these denominators are nonzero.

**Definition 1.13 (Embedding an adjacent two-site operator).**

$$\forall (R : \operatorname{Type}), ([\operatorname{Zero}\left(R\right)]) \to (\forall (n : \mathbb{N}), \forall (N : \mathbb{N}), \forall (m : \operatorname{Fin}\left(N - 1\right)), \forall (P : \operatorname{Matrix}\left((\operatorname{Fin}\left(n + 1\right)) \times (\operatorname{Fin}\left(n + 1\right)), (\operatorname{Fin}\left(n + 1\right)) \times (\operatorname{Fin}\left(n + 1\right)), R\right)), \forall (x : \operatorname{Fin}\left((n + 1)^{N}\right)), \forall (y : \operatorname{Fin}\left((n + 1)^{N}\right)), \operatorname{siteOperator}\left(m, P\right)\left(x, y\right) = \operatorname{ite}\left((\forall (k : \operatorname{Fin}\left(N\right)), (k \ne \operatorname{fin}\left(\operatorname{val}\left(m\right), N\right)) \to ((k \ne \operatorname{fin}\left(\operatorname{val}\left(m\right) + 1, N\right)) \to (\operatorname{digit}\left(x, k\right) = \operatorname{digit}\left(y, k\right)))), P\left((\operatorname{digit}\left(x, \operatorname{fin}\left(\operatorname{val}\left(m\right), N\right)\right), \operatorname{digit}\left(x, \operatorname{fin}\left(\operatorname{val}\left(m\right) + 1, N\right)\right)), (\operatorname{digit}\left(y, \operatorname{fin}\left(\operatorname{val}\left(m\right), N\right)\right), \operatorname{digit}\left(y, \operatorname{fin}\left(\operatorname{val}\left(m\right) + 1, N\right)\right))\right), 0\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.siteOperator` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

The operator P acts at the adjacent positions val(m) and val(m)+1, numbered from zero. Its matrix entry vanishes unless all other tensor digits agree. This is the adjacent-site embedding used before Eq. (Hal), expressed in the base-(n+1) tensor basis.

**Definition 1.14 (The open-chain Hamiltonian).**

$$\forall (n : \mathbb{N}), \forall (s : \mathbb{N}), \forall (N : \mathbb{N}), \forall (\gamma : \mathbb{R}), \forall (a : (\operatorname{Fin}\left(N - 1\right)) \to (\mathbb{R})), \operatorname{hamiltonian}\left(n, s, N, \gamma, a\right) = \sum_{m : \operatorname{Fin}\left(N - 1\right)} (\operatorname{smul}\left(\operatorname{cast}\left(\mathbb{R}, \mathbb{C}, a\left(m\right)\right), \operatorname{siteOperator}\left(m, \operatorname{projector}\left(n, s, \gamma\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.hamiltonian` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

Equation (Hal) sums the adjacent projectors with real couplings. The index m in Fin(N−1) corresponds to the source's bond m+1. Each coupling is coerced from the reals to the complexes before scalar multiplication.

**Definition 1.15 (Positive couplings and the proposed real spectrum).**

$$\operatorname{claim} \Leftrightarrow (\forall (n : \mathbb{N}), \forall (s : \mathbb{N}), \forall (N : \mathbb{N}), \forall (\gamma : \mathbb{R}), (1 \le n) \to ((s \le n) \to ((2 \le N) \to ((0 < \left|\gamma\right|) \to ((\operatorname{cast}\left(\mathbb{N}, \mathbb{R}, n\right) \cdot \left|\gamma\right| < \pi) \to ((\forall (l : \mathbb{N}), (l \le n) \to ((l \ne s) \to (\operatorname{qnum}\left(\gamma, \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, s\right) - \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, l\right)\right) \cdot \operatorname{qnum}\left(\gamma, \operatorname{cast}\left(\mathbb{N}, \mathbb{R}, s + l + 1\right)\right) \ne 0))) \to (\forall (a : (\operatorname{Fin}\left(N - 1\right)) \to (\mathbb{R})), (\forall (m : \operatorname{Fin}\left(N - 1\right)), 0 < a\left(m\right)) \to (\forall (v : (\operatorname{Fin}\left((n + 1)^{N}\right)) \to (\mathbb{C})), \forall (z : \mathbb{C}), (v \ne 0) \to ((\operatorname{mulVec}\left(\operatorname{hamiltonian}\left(n, s, N, \gamma, a\right), v\right) = \operatorname{smul}\left(z, v\right)) \to (\operatorname{im}\left(z\right) = 0))))))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.claim` (`✓ std3`).

*Citation.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

Conjecture 3 asserts a real spectrum for positive couplings when |γ|<π/(2S). Here n=2S≥1, 0≤s≤n and N≥2. The nonzero angle and explicit nonvanishing projector denominators make the formulas applicable. Every nonzero vector v satisfying H v=z v is asserted to have Im(z)=0.

**Theorem 1.16 (A four-site spin-one counterexample).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bytsko-2009-positive-coupling-real-spectrum-refutation` (refuted) by `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bytsko-2009-positive-coupling-real-spectrum-refutation","declaration_gid":"D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. G. Bytsko (2011). *Non-Hermitian spin chains with inhomogeneous coupling*. DOI: [10.1090/S1061-0022-2011-01148-3](https://doi.org/10.1090/S1061-0022-2011-01148-3). URL: <https://arxiv.org/abs/0911.4476v3>.

*Commentary.*

Take S=s=1, hence n=2, N=4, γ=γ₀=arccos(4/5), sin(γ₀)=3/5, q=(4+3i)/5 and a=(1,1,1). These satisfy 0<2|γ|<π, and the two required denominator products, for l=0 and l=2, are 8/5 and −112/125.

Order the two-site basis lexicographically by weights −1,0,1. The matrix 14·P^{1,1} is [[0,0,0,0,0,0,0,0,0], [0,7+24i,0,−25,0,0,0,0,0], [0,0,25,0,30i,0,−25,0,0], [0,−25,0,7−24i,0,0,0,0,0], [0,0,30i,0,−36,0,−30i,0,0], [0,0,0,0,0,7+24i,0,−25,0], [0,0,−25,0,−30i,0,25,0,0], [0,0,0,0,0,−25,0,7−24i,0], [0,0,0,0,0,0,0,0,0]].

Index the four-site basis by x=27i₁+9i₂+3i₃+i₄, with iⱼ∈{0,1,2}. Define the 81-by-2 matrix W by its nonzero rows, whose entries are ordered as columns 0 and 1: 26:(0,4900); 44:(−5500−4125i,3080+8190i); 50:(5500−4125i,−7000+5250i); 62:(8800−6600i,−9828+3696i); 68:(7920+10560i,−10080−13440i); 70:(−5500+4125i,7000−5250i); 74:(−8800+6600i,6300−8400i); 76:(−2420−6435i,7000+5250i); 78:(0,−1372+4704i). All other rows vanish.

Let A=[[-11/14,1],[-275/196,25/14]] and B=[[1,0],[0,0]]. For the adjacent embeddings P₁₂,P₂₃,P₃₄ of P^{1,1}, direct matrix multiplication gives (P₁₂+P₃₄)W=WA and P₂₃W=WB. Therefore HW=W(A+B). Put z=1+i√(11/14)=1+i√(22/7)/2 and y=(1,z−1+11/14). The identity z²−2z+25/14=0 gives (A+B)y=zy. Consequently H(Wy)=z(Wy). The component at x=26 is 4900(z−1+11/14), whose imaginary part is positive; hence Wy is nonzero. Since Im(z)=√(11/14)>0, this positive-coupling chain refutes the universal real-spectrum assertion. The construction uses the algebra and projectors of Bytsko's paper; it does not settle the restriction s=0.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.E`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.F`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.K`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.Kinv`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.casimirValue`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.digit`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.hamiltonian`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.orderedProduct`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.projector`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.q`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.qnum`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.result`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.siteOperator`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.tensorCasimir`
- Truth anchor: `D5/S3/Quantum/SpinChains/QuantumGroupChainRealSpectrumRefutation.weight`
