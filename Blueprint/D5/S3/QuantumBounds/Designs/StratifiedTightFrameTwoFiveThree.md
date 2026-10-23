# A real SUNTF_R(2, 5, 3) exists

## Abstract

An explicit real SUNTF with parameters (D,N,R) = (2,5,3).

Example 4.4, last paragraph (arXiv:2610.05302v1): "We do not yet know whether a SUNTF_R(2, 5, 3) exists, and we leave this for future research." Definition 3.2 (real case) defines a stratified family by constant averaged squared inner products between distinct columns, and a SUNTF when every layer is a unit norm tight frame of common dimension.

**Definition 1.1 (Unit norm tight frames).**

$$\forall D \in \mathbb {N},\; \forall N \in \mathbb {N},\; \forall phi \in \operatorname {Fin}\left(N\right) \to \operatorname {EuclideanSpace}\left(\mathbb {R}, \operatorname {Fin}\left(D\right)\right),\; (\operatorname {IsUNTF}\left(phi\right)) \Leftrightarrow ((\forall n \in \operatorname {Fin}\left(N\right),\; \operatorname {norm}\left(\operatorname {phi}\left(n\right)\right) = 1) \land (\exists A \in \mathbb {R},\; (0 < A) \land (\forall x \in \operatorname {EuclideanSpace}\left(\mathbb {R}, \operatorname {Fin}\left(D\right)\right),\; \sum n (\langle \operatorname {phi}\left(n\right), x \rangle)^{2} = A \cdot (\operatorname {norm}\left(x\right))^{2})))$$

*Formalization.* `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.IsUNTF` (`✓ std3`).

*Citation.* W. J. Brinkley, M. Fickus, J. Jasper and D. G. Mixon (2026). *Incoherent filter banks*. DOI: [10.48550/arXiv.2610.05302](https://doi.org/10.48550/arXiv.2610.05302). URL: <https://arxiv.org/abs/2610.05302v1>.

*Commentary.*

Definition 3.2 requires every vector in a layer to have norm one and requires a positive frame bound A for the sum of squared analysis coefficients. The formal predicate uses EuclideanSpace R (Fin D) and Fin N for the layer.

**Definition 1.2 (Stratified families).**

$$\forall D \in \mathbb {N},\; \forall N \in \mathbb {N},\; \forall R \in \mathbb {N},\; \forall phi \in \operatorname {Fin}\left(R\right) \to \operatorname {Fin}\left(N\right) \to \operatorname {EuclideanSpace}\left(\mathbb {R}, \operatorname {Fin}\left(D\right)\right),\; (\operatorname {IsStratified}\left(phi\right)) \Leftrightarrow (\exists lambda \in \mathbb {R},\; (0 \le lambda) \land (\forall n1 \in \operatorname {Fin}\left(N\right),\; \forall n2 \in \operatorname {Fin}\left(N\right),\; (\neg n1 = n2) \Rightarrow (\frac{1}{\operatorname {NatCast}\left(R\right)} \cdot \sum r (\langle \operatorname {phi}\left(r, n1\right), \operatorname {phi}\left(r, n2\right) \rangle)^{2} = lambda)))$$

*Formalization.* `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.IsStratified` (`✓ std3`).

*Citation.* W. J. Brinkley, M. Fickus, J. Jasper and D. G. Mixon (2026). *Incoherent filter banks*. DOI: [10.48550/arXiv.2610.05302](https://doi.org/10.48550/arXiv.2610.05302). URL: <https://arxiv.org/abs/2610.05302v1>.

*Commentary.*

Definition 3.2 (arXiv:2610.05302v1, Section 3, p. 8) states: "Let N and R be finite sets of cardinality N > 0 and R > 0, respectively. For each r ∈ R, let (φ_{r,n})_{n∈N} be a finite sequence of unit vectors in a Euclidean space E_r over F. We say (φ_{r,n})_{n∈N, r∈R} is stratified if there exists Λ ≥ 0 such that (1/R) Σ_{r∈R} |⟨φ_{r,n1}, φ_{r,n2}⟩|² = Λ for any distinct n1, n2 ∈ N. If this holds and each layer (φ_{r,n})_{n∈N} is a UNTF for E_r where there exists D > 0 such that dim(E_r) = D for any r ∈ R, we call (φ_{r,n})_{n∈N, r∈R} a SUNTF for (E_r)_{r∈R} or a SUNTF_F(D, N, R)." Over the real field the absolute values may be represented by squares.

**Definition 1.3 (SUNTF families).**

$$\forall D \in \mathbb {N},\; \forall N \in \mathbb {N},\; \forall R \in \mathbb {N},\; \forall phi \in \operatorname {Fin}\left(R\right) \to \operatorname {Fin}\left(N\right) \to \operatorname {EuclideanSpace}\left(\mathbb {R}, \operatorname {Fin}\left(D\right)\right),\; (\operatorname {IsSUNTF}\left(phi\right)) \Leftrightarrow ((\forall r \in \operatorname {Fin}\left(R\right),\; \operatorname {IsUNTF}\left(\operatorname {phi}\left(r\right)\right)) \land (\operatorname {IsStratified}\left(phi\right)))$$

*Formalization.* `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.IsSUNTF` (`✓ std3`).

*Citation.* W. J. Brinkley, M. Fickus, J. Jasper and D. G. Mixon (2026). *Incoherent filter banks*. DOI: [10.48550/arXiv.2610.05302](https://doi.org/10.48550/arXiv.2610.05302). URL: <https://arxiv.org/abs/2610.05302v1>.

*Commentary.*

A SUNTF_R(D,N,R) is a stratified family whose R layers are unit norm tight frames for real D-dimensional Euclidean spaces.

**Definition 1.4 (The nonexistence question).**

$$(claim) \Leftrightarrow (\neg \left(\exists phi \in \operatorname {Fin}\left(3\right) \to \operatorname {Fin}\left(5\right) \to \operatorname {EuclideanSpace}\left(\mathbb {R}, \operatorname {Fin}\left(2\right)\right),\; \operatorname {IsSUNTF}\left(phi\right)\right))$$

*Formalization.* `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.claim` (`✓ std3`).

*Citation.* W. J. Brinkley, M. Fickus, J. Jasper and D. G. Mixon (2026). *Incoherent filter banks*. DOI: [10.48550/arXiv.2610.05302](https://doi.org/10.48550/arXiv.2610.05302). URL: <https://arxiv.org/abs/2610.05302v1>.

*Commentary.*

The paper asks whether a SUNTF_R(2, 5, 3) exists. The encoded claim is the negation of that existence statement, so refuting claim proves the requested existence.

**Theorem 1.5 (The construction exists).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/brinkley-fickus-jasper-mixon-2026-suntf-two-five-three` (proved) by `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"brinkley-fickus-jasper-mixon-2026-suntf-two-five-three","declaration_gid":"D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* W. J. Brinkley, M. Fickus, J. Jasper and D. G. Mixon (2026). *Incoherent filter banks*. DOI: [10.48550/arXiv.2610.05302](https://doi.org/10.48550/arXiv.2610.05302). URL: <https://arxiv.org/abs/2610.05302v1>.

*Commentary.*

Take u = √(3/8) and v = √(5/8). The three layers use the columns (1,0), (u,v), (u,−v), (u,−v), (u,v); (1,0), (u,v), (u,−v), (u,v), (u,−v); and (1,0), (u,v), (u,v), (u,−v), (u,−v). Each layer has unit norms and frame bound 5/2. Across the three layers, the sign words of the four non-anchor columns, namely (+,+,+), (−,−,+), (−,+,−), (+,−,−) (each of length three), agree pairwise in exactly one position, so every averaged squared inner product is 3/8. These exact finite computations refute the encoded nonexistence claim.

## References

- Truth anchor: `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.IsSUNTF`
- Truth anchor: `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.IsStratified`
- Truth anchor: `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.IsUNTF`
- Truth anchor: `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.claim`
- Truth anchor: `D5/S3/QuantumBounds/Designs/StratifiedTightFrameTwoFiveThree.result`
