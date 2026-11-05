# A dense-square Hilbert algebra with two different natural orthonormal bases

## Abstract

Dense algebraic square does not force uniqueness of a complete natural orthonormal basis of a Hilbert evolution algebra.

Question 46 in section 2.2.8 of Kaygorodov, Martin Gonzalez and Viruel asks: If the square of a Hilbert evolution algebra is dense, is its natural orthonormal basis unique up to permutation and unimodular scalars? The square means the algebraic span of all products; density and completeness use the Hilbert norm. Definition 2.2 of Vidal, Cadavid and Rodriguez permits real or complex scalars and requires bounded left multiplication for every fixed vector. The two scalar cases are conjoined in claim. Its complex branch alone fails. The separate questions about derivations, automorphisms and spectral theory are outside this assertion.

The witness space is the complex square-summable sequence space lp on all positive integers at exponent two, with its standard norm and inner product. It is complete and separable. The standard orthonormal family has closed linear span equal to the whole space; no algebraic Hamel basis is used.

**Definition 1.1 (The standard complete orthonormal basis).**

$$e = \operatorname{HilbertBasis}.\operatorname{ofRepr}\left(\operatorname{LinearIsometryEquiv}.\operatorname{refl}\left(Complex, \operatorname{lp}\left(\operatorname{Function}.\operatorname{const}\left(PNat, Complex\right), 2\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.e` (`✓ std3`).

*Citation.* Sebastian J. Vidal; Paula Cadavid; Pablo M. Rodriguez (2020). *Hilbert evolution algebras and its connection with discrete-time Markov chains*. DOI: [10.48550/arXiv.2012.05124](https://doi.org/10.48550/arXiv.2012.05124). URL: <https://arxiv.org/abs/2012.05124v2>.

*Commentary.*

The identity isometric representation of the sequence space supplies e. Each e(i) is the sequence with coordinate one at i and zero elsewhere.

**Definition 1.2 (A continuous complex-bilinear multiplication).**

$$mu \in \operatorname{ContinuousLinearMap}\left(Complex, \operatorname{lp}\left(\operatorname{Function}.\operatorname{const}\left(PNat, Complex\right), 2\right), \operatorname{ContinuousLinearMap}\left(Complex, \operatorname{lp}\left(\operatorname{Function}.\operatorname{const}\left(PNat, Complex\right), 2\right), \operatorname{lp}\left(\operatorname{Function}.\operatorname{const}\left(PNat, Complex\right), 2\right)\right)\right) \land \left(\forall x \in \operatorname{lp}\left(\operatorname{Function}.\operatorname{const}\left(PNat, Complex\right), 2\right),\; \forall y \in \operatorname{lp}\left(\operatorname{Function}.\operatorname{const}\left(PNat, Complex\right), 2\right),\; mu\left(x, y\right) = \operatorname{tsum}\left(fun (i:PNat) \mapsto x\left(i\right) \cdot y\left(i\right) \cdot e\left(\operatorname{ite}\left(i = 1, 1, i-1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.mu` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yolanda Cabrera Casado; Maria Inez Cardoso Goncalves; Daniel Goncalves; Dolores Martin Barquero; Candido Martin Gonzalez; Ivan Ruiz Campos (2025). *Solenoids in automorphism groups of evolution algebras*. DOI: [10.48550/arXiv.2505.14584](https://doi.org/10.48550/arXiv.2505.14584). URL: <https://arxiv.org/abs/2505.14584v1>.

*Acknowledgement.* Sebastian J. Vidal; Paula Cadavid; Pablo M. Rodriguez (2020). *Hilbert evolution algebras and its connection with discrete-time Markov chains*. DOI: [10.48550/arXiv.2012.05124](https://doi.org/10.48550/arXiv.2012.05124). URL: <https://arxiv.org/abs/2012.05124v2>.

*Commentary.*

The series converges in the sequence space by the lp.dualPairing construction from uniformly bounded coordinate bilinear maps and the two-two Holder pairing. Scalar multiplication is complex-linear in both inputs: the coefficient is x(i)y(i), without conjugation. The table is e(1)^2=e(2)^2=e(1) and e(i+1)^2=e(i), with every mixed standard-basis product zero. This table is Example 3.7 of Solenoids in automorphism groups of evolution algebras. For each v the positive number norm(mu(v))+1 bounds left multiplication on every w. Joint continuity of this particular product is stronger than the left-multiplication requirement.

**Definition 1.3 (The second complete orthonormal basis).**

$$f \in \operatorname{HilbertBasis}\left(PNat, Complex, \operatorname{lp}\left(\operatorname{Function}.\operatorname{const}\left(PNat, Complex\right), 2\right)\right) \land \left(\forall i \in PNat,\; f\left(i\right) = \operatorname{ite}\left(i = 1, \frac{3}{5} \cdot e\left(1\right) + \frac{4}{5} \cdot e\left(2\right), \operatorname{ite}\left(i = 2, \frac{-4}{5} \cdot e\left(1\right) + \frac{3}{5} \cdot e\left(2\right), e\left(i\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.f` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paula Cadavid; Pablo M. Rodriguez; Sebastian J. Vidal (2023). *Hilbert evolution algebras, weighted digraphs, and nilpotency*. DOI: [10.48550/arXiv.2311.08387](https://doi.org/10.48550/arXiv.2311.08387). URL: <https://arxiv.org/abs/2311.08387v2>.

*Commentary.*

Only the first two basis vectors change. The real coefficients 3/5 and 4/5 satisfy 9/25+16/25=1, so this block is unitary over the complex scalars. Its inverse gives e(1)=(3/5)f(1)-(4/5)f(2) and e(2)=(4/5)f(1)+(3/5)f(2); all other vectors agree. Thus the closed span is the whole sequence space. Since e(1)^2=e(2)^2, the two mixed terms cancel and f is natural for the same multiplication. The equal-square rotation method occurs in Examples 3.6-3.7 of Hilbert evolution algebras, weighted digraphs, and nilpotency.

**Definition 1.4 (The scalar-specific universal assertion).**

$$\forall k \in Type,\; [\operatorname{RCLike}\left(k\right)], \operatorname{uniqueness}\left(k\right) \Leftrightarrow \left(\forall A \in Type,\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{InnerProductSpace}\left(k, A\right)] [\operatorname{CompleteSpace}\left(A\right)] [\operatorname{SeparableSpace}\left(A\right)], \forall m \in \operatorname{LinearMap}\left(k, A, \operatorname{LinearMap}\left(k, A, A\right)\right),\; \forall a \in \operatorname{HilbertBasis}\left(PNat, k, A\right),\; \forall b \in \operatorname{HilbertBasis}\left(PNat, k, A\right),\; \left(\forall v \in A,\; \exists M \in Real,\; 0 < M \land \left(\forall w \in A,\; \left\lVert m\left(v, w\right) \right\rVert \le M \cdot \left\lVert w \right\rVert\right)\right) \Rightarrow \left(\left(\forall i \in PNat,\; \forall j \in PNat,\; i \ne j \Rightarrow m\left(a\left(i\right), a\left(j\right)\right) = 0\right) \Rightarrow \left(\left(\forall i \in PNat,\; \forall j \in PNat,\; i \ne j \Rightarrow m\left(b\left(i\right), b\left(j\right)\right) = 0\right) \Rightarrow \left(\operatorname{Submodule}.\operatorname{topologicalClosure}\left(\operatorname{Submodule}.\operatorname{span}\left(k, \{z:A \mid \exists x \in A,\; \exists y \in A,\; m\left(x, y\right) = z\}\right)\right) = \operatorname{Top}.\operatorname{top} \Rightarrow \left(\exists sigma \in \operatorname{Equiv}.\operatorname{Perm}\left(PNat\right),\; \exists c \in PNat \to k,\; \left(\forall i \in PNat,\; \left\lVert c\left(i\right) \right\rVert = 1\right) \land \left(\forall i \in PNat,\; b\left(i\right) = c\left(i\right) \cdot a\left(sigma\left(i\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.uniqueness` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

All complete separable Hilbert spaces over k, all bilinear products with the stated positive left bounds, and both complete natural orthonormal bases are quantified. A dense square is the only extra premise. The conclusion allows every permutation of the positive integers and every scalar family of norm one. The bracketed assumptions denote the corresponding chosen Lean structures or instances. RCLike supplies the real and complex specializations used in claim.

**Definition 1.5 (The entire real-or-complex source assertion).**

$$claim \Leftrightarrow \left(\left(\forall A \in Type,\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{InnerProductSpace}\left(Real, A\right)] [\operatorname{CompleteSpace}\left(A\right)] [\operatorname{SeparableSpace}\left(A\right)], \forall m \in \operatorname{LinearMap}\left(Real, A, \operatorname{LinearMap}\left(Real, A, A\right)\right),\; \forall a \in \operatorname{HilbertBasis}\left(PNat, Real, A\right),\; \forall b \in \operatorname{HilbertBasis}\left(PNat, Real, A\right),\; \left(\forall v \in A,\; \exists M \in Real,\; 0 < M \land \left(\forall w \in A,\; \left\lVert m\left(v, w\right) \right\rVert \le M \cdot \left\lVert w \right\rVert\right)\right) \Rightarrow \left(\left(\forall i \in PNat,\; \forall j \in PNat,\; i \ne j \Rightarrow m\left(a\left(i\right), a\left(j\right)\right) = 0\right) \Rightarrow \left(\left(\forall i \in PNat,\; \forall j \in PNat,\; i \ne j \Rightarrow m\left(b\left(i\right), b\left(j\right)\right) = 0\right) \Rightarrow \left(\operatorname{Submodule}.\operatorname{topologicalClosure}\left(\operatorname{Submodule}.\operatorname{span}\left(Real, \{z:A \mid \exists x \in A,\; \exists y \in A,\; m\left(x, y\right) = z\}\right)\right) = \operatorname{Top}.\operatorname{top} \Rightarrow \left(\exists sigma \in \operatorname{Equiv}.\operatorname{Perm}\left(PNat\right),\; \exists c \in PNat \to Real,\; \left(\forall i \in PNat,\; \left\lVert c\left(i\right) \right\rVert = 1\right) \land \left(\forall i \in PNat,\; b\left(i\right) = c\left(i\right) \cdot a\left(sigma\left(i\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\forall A \in Type,\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{InnerProductSpace}\left(Complex, A\right)] [\operatorname{CompleteSpace}\left(A\right)] [\operatorname{SeparableSpace}\left(A\right)], \forall m \in \operatorname{LinearMap}\left(Complex, A, \operatorname{LinearMap}\left(Complex, A, A\right)\right),\; \forall a \in \operatorname{HilbertBasis}\left(PNat, Complex, A\right),\; \forall b \in \operatorname{HilbertBasis}\left(PNat, Complex, A\right),\; \left(\forall v \in A,\; \exists M \in Real,\; 0 < M \land \left(\forall w \in A,\; \left\lVert m\left(v, w\right) \right\rVert \le M \cdot \left\lVert w \right\rVert\right)\right) \Rightarrow \left(\left(\forall i \in PNat,\; \forall j \in PNat,\; i \ne j \Rightarrow m\left(a\left(i\right), a\left(j\right)\right) = 0\right) \Rightarrow \left(\left(\forall i \in PNat,\; \forall j \in PNat,\; i \ne j \Rightarrow m\left(b\left(i\right), b\left(j\right)\right) = 0\right) \Rightarrow \left(\operatorname{Submodule}.\operatorname{topologicalClosure}\left(\operatorname{Submodule}.\operatorname{span}\left(Complex, \{z:A \mid \exists x \in A,\; \exists y \in A,\; m\left(x, y\right) = z\}\right)\right) = \operatorname{Top}.\operatorname{top} \Rightarrow \left(\exists sigma \in \operatorname{Equiv}.\operatorname{Perm}\left(PNat\right),\; \exists c \in PNat \to Complex,\; \left(\forall i \in PNat,\; \left\lVert c\left(i\right) \right\rVert = 1\right) \land \left(\forall i \in PNat,\; b\left(i\right) = c\left(i\right) \cdot a\left(sigma\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.claim` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Question 46, page 26: If the square of a Hilbert evolution algebra is dense, is its natural orthonormal basis unique up to permutation and unimodular scalars? The real universal assertion and the complex universal assertion are both required. Their conjunction faithfully states the first interrogative under the complete Hilbert-space convention. The complex assertion alone is a consequence of this conjunction; they are not asserted equivalent.

**Theorem 1.6 (Refutation by the complex Hilbert example).**

$$\neg \left(\left(\forall A \in Type,\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{InnerProductSpace}\left(Real, A\right)] [\operatorname{CompleteSpace}\left(A\right)] [\operatorname{SeparableSpace}\left(A\right)], \forall m \in \operatorname{LinearMap}\left(Real, A, \operatorname{LinearMap}\left(Real, A, A\right)\right),\; \forall a \in \operatorname{HilbertBasis}\left(PNat, Real, A\right),\; \forall b \in \operatorname{HilbertBasis}\left(PNat, Real, A\right),\; \left(\forall v \in A,\; \exists M \in Real,\; 0 < M \land \left(\forall w \in A,\; \left\lVert m\left(v, w\right) \right\rVert \le M \cdot \left\lVert w \right\rVert\right)\right) \Rightarrow \left(\left(\forall i \in PNat,\; \forall j \in PNat,\; i \ne j \Rightarrow m\left(a\left(i\right), a\left(j\right)\right) = 0\right) \Rightarrow \left(\left(\forall i \in PNat,\; \forall j \in PNat,\; i \ne j \Rightarrow m\left(b\left(i\right), b\left(j\right)\right) = 0\right) \Rightarrow \left(\operatorname{Submodule}.\operatorname{topologicalClosure}\left(\operatorname{Submodule}.\operatorname{span}\left(Real, \{z:A \mid \exists x \in A,\; \exists y \in A,\; m\left(x, y\right) = z\}\right)\right) = \operatorname{Top}.\operatorname{top} \Rightarrow \left(\exists sigma \in \operatorname{Equiv}.\operatorname{Perm}\left(PNat\right),\; \exists c \in PNat \to Real,\; \left(\forall i \in PNat,\; \left\lVert c\left(i\right) \right\rVert = 1\right) \land \left(\forall i \in PNat,\; b\left(i\right) = c\left(i\right) \cdot a\left(sigma\left(i\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\forall A \in Type,\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{InnerProductSpace}\left(Complex, A\right)] [\operatorname{CompleteSpace}\left(A\right)] [\operatorname{SeparableSpace}\left(A\right)], \forall m \in \operatorname{LinearMap}\left(Complex, A, \operatorname{LinearMap}\left(Complex, A, A\right)\right),\; \forall a \in \operatorname{HilbertBasis}\left(PNat, Complex, A\right),\; \forall b \in \operatorname{HilbertBasis}\left(PNat, Complex, A\right),\; \left(\forall v \in A,\; \exists M \in Real,\; 0 < M \land \left(\forall w \in A,\; \left\lVert m\left(v, w\right) \right\rVert \le M \cdot \left\lVert w \right\rVert\right)\right) \Rightarrow \left(\left(\forall i \in PNat,\; \forall j \in PNat,\; i \ne j \Rightarrow m\left(a\left(i\right), a\left(j\right)\right) = 0\right) \Rightarrow \left(\left(\forall i \in PNat,\; \forall j \in PNat,\; i \ne j \Rightarrow m\left(b\left(i\right), b\left(j\right)\right) = 0\right) \Rightarrow \left(\operatorname{Submodule}.\operatorname{topologicalClosure}\left(\operatorname{Submodule}.\operatorname{span}\left(Complex, \{z:A \mid \exists x \in A,\; \exists y \in A,\; m\left(x, y\right) = z\}\right)\right) = \operatorname{Top}.\operatorname{top} \Rightarrow \left(\exists sigma \in \operatorname{Equiv}.\operatorname{Perm}\left(PNat\right),\; \exists c \in PNat \to Complex,\; \left(\forall i \in PNat,\; \left\lVert c\left(i\right) \right\rVert = 1\right) \land \left(\forall i \in PNat,\; b\left(i\right) = c\left(i\right) \cdot a\left(sigma\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.result` (`✓ std3`). ∎

*Resolves.* `Problems/kaygorodov-martin-gonzalez-viruel-2026-hilbert-natural-basis-uniqueness` (refuted) by `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kaygorodov-martin-gonzalez-viruel-2026-hilbert-natural-basis-uniqueness","declaration_gid":"D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Acknowledgement.* Yolanda Cabrera Casado; Maria Inez Cardoso Goncalves; Daniel Goncalves; Dolores Martin Barquero; Candido Martin Gonzalez; Ivan Ruiz Campos (2025). *Solenoids in automorphism groups of evolution algebras*. DOI: [10.48550/arXiv.2505.14584](https://doi.org/10.48550/arXiv.2505.14584). URL: <https://arxiv.org/abs/2505.14584v1>.

*Acknowledgement.* Sebastian J. Vidal; Paula Cadavid; Pablo M. Rodriguez (2020). *Hilbert evolution algebras and its connection with discrete-time Markov chains*. DOI: [10.48550/arXiv.2012.05124](https://doi.org/10.48550/arXiv.2012.05124). URL: <https://arxiv.org/abs/2012.05124v2>.

*Acknowledgement.* Paula Cadavid; Pablo M. Rodriguez; Sebastian J. Vidal (2023). *Hilbert evolution algebras, weighted digraphs, and nilpotency*. DOI: [10.48550/arXiv.2311.08387](https://doi.org/10.48550/arXiv.2311.08387). URL: <https://arxiv.org/abs/2311.08387v2>.

*Commentary.*

Apply the complex universal assertion to the sequence space, mu, e and f. Every standard vector e(i) is the product mu(e(i+1),e(i+1)), so the algebraic product span contains the standard span and its norm closure is the whole space. Both bases are complete, orthonormal and natural. However, f(1) has two nonzero standard coordinates and differs from c times e(j) for every positive j and every complex c. Any proposed permutation and unimodular scalar family would give such an equality at index one. This contradiction refutes the complex assertion and hence the real-or-complex conjunction. The equal-square pair is the failure mechanism: dense square does not forbid two equal nonzero basis squares.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.claim`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.e`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.f`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.mu`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.result`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/HilbertNaturalBasisNonuniqueness.uniqueness`
