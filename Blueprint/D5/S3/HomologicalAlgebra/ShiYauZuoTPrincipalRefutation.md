# A finite-field counterexample to the T-principality criterion

## Abstract

A binary square-zero local algebra refutes Shi-Yau-Zuo Conjecture 4.79.

**Definition 1.1 (Ideal of component values).**

$$\forall \{F : \operatorname{Type}\} [\operatorname{Field}\left(F\right)] \{A : \operatorname{Type}\} [\operatorname{CommRing}\left(A\right)] [\operatorname{Algebra}\left(F, A\right)] \{n : \mathbb{N}\} (components : \operatorname{Fin}\left(n\right) \to A \to_{l[F]} A) (f : A), \operatorname{valueIdeal}\left(components, f\right) : \operatorname{Ideal}\left(A\right) = \operatorname{Ideal.span}\left(\operatorname{Set.range}\left(\lambda j, components\left(j, f\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.valueIdeal` (`✓ std3`).

*Citation.* Quan Shi; Stephen S.-T. Yau; Huaiqing Zuo (2024). *On T-maps and ideals of antiderivatives of hypersurface singularities*. DOI: [10.4213/im9488e](https://doi.org/10.4213/im9488e). URL: <https://m.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9488&what=fullteng&option_lang=eng#page=33>.

*Commentary.*

Definition 4.1 takes the ideal span of the values of a finite family of F-linear endomorphisms.

**Definition 1.2 (T-maps).**

$$\forall (F : \operatorname{Type}) [\operatorname{Field}\left(F\right)] (A : \operatorname{Type}) [\operatorname{CommRing}\left(A\right)] [\operatorname{Algebra}\left(F, A\right)], \operatorname{TMap}\left(F, A\right) : \operatorname{Type}\quad\{\operatorname{count} : \mathbb{N}, \operatorname{components} : \operatorname{Fin}\left(\operatorname{count}\right) \to A \to_{l[F]} A, \operatorname{mul}_{\operatorname{le}} : \forall a f : A, \operatorname{valueIdeal}\left(\operatorname{components}, a \cdot f\right) \le \operatorname{valueIdeal}\left(\operatorname{components}, f\right)\}$$

*Formalization.* `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.TMap` (`✓ std3`).

*Citation.* Quan Shi; Stephen S.-T. Yau; Huaiqing Zuo (2024). *On T-maps and ideals of antiderivatives of hypersurface singularities*. DOI: [10.4213/im9488e](https://doi.org/10.4213/im9488e). URL: <https://m.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9488&what=fullteng&option_lang=eng#page=33>.

*Commentary.*

Definition 4.1 and Remark 4.3 keep the F-linear maps as data. The fields count and components specify their number and family. The field mul_le requires Q(af) ⊆ Q(f) for every a and f in A.

**Definition 1.3 (Image ideal).**

$$\forall \{F : \operatorname{Type}\} [\operatorname{Field}\left(F\right)] \{A : \operatorname{Type}\} [\operatorname{CommRing}\left(A\right)] [\operatorname{Algebra}\left(F, A\right)] (Q : \operatorname{TMap}\left(F, A\right)) (J : \operatorname{Ideal}\left(A\right)), \operatorname{imageIdeal}\left(Q, J\right) : \operatorname{Ideal}\left(A\right) = \operatorname{sSup}\left(\{\operatorname{valueIdeal}\left(\operatorname{TMap.components}\left(Q\right), f\right) \mid f \in J\}\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.imageIdeal` (`✓ std3`).

*Citation.* Quan Shi; Stephen S.-T. Yau; Huaiqing Zuo (2024). *On T-maps and ideals of antiderivatives of hypersurface singularities*. DOI: [10.4213/im9488e](https://doi.org/10.4213/im9488e). URL: <https://m.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9488&what=fullteng&option_lang=eng#page=33>.

*Commentary.*

Definition 4.6 sums the value ideals over all elements of J. For generators of J it equals the sum of their value ideals, by linearity and the multiplication law.

**Definition 1.4 (Ideal of antiderivatives).**

$$\forall \{F : \operatorname{Type}\} [\operatorname{Field}\left(F\right)] \{A : \operatorname{Type}\} [\operatorname{CommRing}\left(A\right)] [\operatorname{Algebra}\left(F, A\right)] (Q : \operatorname{TMap}\left(F, A\right)) (I : \operatorname{Ideal}\left(A\right)), \operatorname{delta}\left(Q, I\right) : \operatorname{Ideal}\left(A\right) = \{f : A \mid \operatorname{valueIdeal}\left(\operatorname{TMap.components}\left(Q\right), f\right) \le I\}$$

*Formalization.* `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.delta` (`✓ std3`).

*Citation.* Quan Shi; Stephen S.-T. Yau; Huaiqing Zuo (2024). *On T-maps and ideals of antiderivatives of hypersurface singularities*. DOI: [10.4213/im9488e](https://doi.org/10.4213/im9488e). URL: <https://m.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9488&what=fullteng&option_lang=eng#page=33>.

*Commentary.*

Definition 4.8 collects the elements whose value ideals are contained in I. Linearity and the multiplication law give the ideal operations, as in Remark 4.9.

**Definition 1.5 (T-principality).**

$$\forall \{F : \operatorname{Type}\} [\operatorname{Field}\left(F\right)] \{A : \operatorname{Type}\} [\operatorname{CommRing}\left(A\right)] [\operatorname{Algebra}\left(F, A\right)] (Q : \operatorname{TMap}\left(F, A\right)) (I : \operatorname{Ideal}\left(A\right)), \operatorname{TPrincipal}\left(Q, I\right) \iff \exists f : A, I = \operatorname{valueIdeal}\left(\operatorname{TMap.components}\left(Q\right), f\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.TPrincipal` (`✓ std3`).

*Citation.* Quan Shi; Stephen S.-T. Yau; Huaiqing Zuo (2024). *On T-maps and ideals of antiderivatives of hypersurface singularities*. DOI: [10.4213/im9488e](https://doi.org/10.4213/im9488e). URL: <https://m.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9488&what=fullteng&option_lang=eng#page=33>.

*Commentary.*

The paragraph after Example 4.5 calls I T-principal when it is the value ideal of one element.

**Definition 1.6 (T-fullness).**

$$\forall \{F : \operatorname{Type}\} [\operatorname{Field}\left(F\right)] \{A : \operatorname{Type}\} [\operatorname{CommRing}\left(A\right)] [\operatorname{Algebra}\left(F, A\right)] (Q : \operatorname{TMap}\left(F, A\right)) (I : \operatorname{Ideal}\left(A\right)), \operatorname{TFull}\left(Q, I\right) \iff \operatorname{imageIdeal}\left(Q, \operatorname{delta}\left(Q, I\right)\right) = I$$

*Formalization.* `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.TFull` (`✓ std3`).

*Citation.* Quan Shi; Stephen S.-T. Yau; Huaiqing Zuo (2024). *On T-maps and ideals of antiderivatives of hypersurface singularities*. DOI: [10.4213/im9488e](https://doi.org/10.4213/im9488e). URL: <https://m.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9488&what=fullteng&option_lang=eng#page=33>.

*Commentary.*

Definition 4.66 requires the image of the antiderivative ideal to be I.

**Definition 1.7 (Generic linear combination).**

$$\forall \{A : \operatorname{Type}\} [\operatorname{CommRing}\left(A\right)] \{r : \mathbb{N}\} (g : \operatorname{Fin}\left(r\right) \to A), \operatorname{genericElement}\left(g\right) : \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(r\right), A\right) = \sum_{i : \operatorname{Fin}\left(r\right)} \operatorname{MvPolynomial.C}\left(g\left(i\right)\right) \operatorname{MvPolynomial.X}\left(i\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.genericElement` (`✓ std3`).

*Citation.* Quan Shi; Stephen S.-T. Yau; Huaiqing Zuo (2024). *On T-maps and ideals of antiderivatives of hypersurface singularities*. DOI: [10.4213/im9488e](https://doi.org/10.4213/im9488e). URL: <https://m.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9488&what=fullteng&option_lang=eng#page=33>.

*Commentary.*

Definition 4.68 attaches one independent variable to each coefficient from the generating tuple.

**Definition 1.8 (Coefficientwise image of the generic element).**

$$\forall \{F : \operatorname{Type}\} [\operatorname{Field}\left(F\right)] \{A : \operatorname{Type}\} [\operatorname{CommRing}\left(A\right)] [\operatorname{Algebra}\left(F, A\right)] \{r : \mathbb{N}\} (Q : \operatorname{TMap}\left(F, A\right)) (g : \operatorname{Fin}\left(r\right) \to A), \operatorname{genericImage}\left(Q, g\right) : \operatorname{Ideal}\left(\operatorname{MvPolynomial}\left(\operatorname{Fin}\left(r\right), A\right)\right) = \operatorname{Ideal.span}\left(\operatorname{Set.range}\left(\lambda j, \operatorname{Finsupp.sum}\left(\operatorname{AddMonoidAlgebra.coeff}\left(\operatorname{genericElement}\left(g\right)\right), \lambda d a, \operatorname{MvPolynomial.monomial}\left(d, \operatorname{TMap.components}\left(Q, j, a\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.genericImage` (`✓ std3`).

*Citation.* Quan Shi; Stephen S.-T. Yau; Huaiqing Zuo (2024). *On T-maps and ideals of antiderivatives of hypersurface singularities*. DOI: [10.4213/im9488e](https://doi.org/10.4213/im9488e). URL: <https://m.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9488&what=fullteng&option_lang=eng#page=33>.

*Commentary.*

The sum runs over the finitely supported coefficient function of the generic element. Each component acts on the coefficients and leaves the monomial exponents fixed. Its value on the generic element is the sum of Qⱼ(gᵢ) times Xᵢ, by additivity and preservation of zero.

**Definition 1.9 (T-dependence by the polynomial colon).**

$$\forall \{F : \operatorname{Type}\} [\operatorname{Field}\left(F\right)] \{A : \operatorname{Type}\} [\operatorname{CommRing}\left(A\right)] [\operatorname{Algebra}\left(F, A\right)] [\operatorname{IsLocalRing}\left(A\right)] (Q : \operatorname{TMap}\left(F, A\right)) (J : \operatorname{Ideal}\left(A\right)), \operatorname{TDependent}\left(Q, J\right) \iff \exists (r : \mathbb{N}) (g : \operatorname{Fin}\left(r\right) \to A), \operatorname{Ideal.span}\left(\operatorname{Set.range}\left(g\right)\right) = J \land \neg (\operatorname{Submodule.colon}\left(\operatorname{genericImage}\left(Q, g\right), (\operatorname{SetLike.coe}\left(\operatorname{Ideal.map}\left((\operatorname{MvPolynomial.C} : A \to^{+*} \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(r\right), A\right)), \operatorname{imageIdeal}\left(Q, J\right)\right)\right) : \operatorname{Set}\left(\operatorname{MvPolynomial}\left(\operatorname{Fin}\left(r\right), A\right)\right))\right) \le \operatorname{Ideal.map}\left((\operatorname{MvPolynomial.C} : A \to^{+*} \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(r\right), A\right)), \operatorname{IsLocalRing.maximalIdeal}\left(A\right)\right))$$

*Formalization.* `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.TDependent` (`✓ std3`).

*Citation.* Quan Shi; Stephen S.-T. Yau; Huaiqing Zuo (2024). *On T-maps and ideals of antiderivatives of hypersurface singularities*. DOI: [10.4213/im9488e](https://doi.org/10.4213/im9488e). URL: <https://m.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9488&what=fullteng&option_lang=eng#page=33>.

*Commentary.*

Definition 4.68 tests whether the colon of the generic image by the extended image ideal escapes the extended maximal ideal. Both extensions use the coefficient inclusion C into the same polynomial ring. Proposition 4.69 gives independence of the generators. In the Noetherian setting a finite tuple exists, so the test can use any one such tuple.

**Definition 1.10 (Conjecture 4.79).**

$$\operatorname{claim} : \operatorname{Prop} = (\forall (F : \operatorname{Type}) [\operatorname{Field}\left(F\right)] (A : \operatorname{Type}) [\operatorname{CommRing}\left(A\right)] [\operatorname{Algebra}\left(F, A\right)] [\operatorname{IsLocalRing}\left(A\right)] [\operatorname{IsNoetherianRing}\left(A\right)], \operatorname{Nonempty}\left(\operatorname{IsLocalRing.ResidueField}\left(A\right) \sim_{\operatorname{Alg}[F]} F\right) \to \forall (Q : \operatorname{TMap}\left(F, A\right)) (I : \operatorname{Ideal}\left(A\right)), \operatorname{TPrincipal}\left(Q, I\right) \iff \operatorname{TFull}\left(Q, I\right) \land \operatorname{TDependent}\left(Q, \operatorname{delta}\left(Q, I\right)\right))$$

*Formalization.* `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.claim` (`✓ std3`).

*Citation.* Quan Shi; Stephen S.-T. Yau; Huaiqing Zuo (2024). *On T-maps and ideals of antiderivatives of hypersurface singularities*. DOI: [10.4213/im9488e](https://doi.org/10.4213/im9488e). URL: <https://m.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9488&what=fullteng&option_lang=eng#page=33>.

*Commentary.*

The conjecture is in §4.6, printed English p. 1217 and original-edition p. 222. The residue field is the native quotient by the maximal ideal. The hypothesis identifies it with F by an F-algebra equivalence, as used by the source's coefficient projection. The proposition includes both implications over an arbitrary field.

**Theorem 1.11 (Refutation of the arbitrary-field biconditional).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Quan Shi; Stephen S.-T. Yau; Huaiqing Zuo (2024). *On T-maps and ideals of antiderivatives of hypersurface singularities*. DOI: [10.4213/im9488e](https://doi.org/10.4213/im9488e). URL: <https://m.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=9488&what=fullteng&option_lang=eng#page=33>.

*Commentary.*

Take A = TrivSqZeroExt (ZMod 2) (Fin 3 → ZMod 2). The scalar projection identifies its residue field with ZMod 2 as an algebra over ZMod 2. Its kernel I has square zero and is the maximal ideal. Each of the three components keeps the scalar part and places u, v, or u + v on its own axis. On the maximal ideal multiplication acts through the scalar part. Away from it the component values are units, so the T-map law holds. The three axes give Δ(I) = Q(I) = I. For the axis generators, the generic image has generators C(e₀)U, C(e₁)V, and C(e₂)(U + V). Multiplying each by the complementary factors in UV(U + V) puts the product times its axis in the generic image. The polynomial survives coefficient reduction because U, V, and U + V are nonzero in the polynomial domain over ZMod 2. Every binary pair makes at least one of u, v, and u + v zero, and scalar multiplication preserves the missing coordinate. Thus no element of I generates I via Q, while a unit gives the whole ring. This finite example refutes the reverse implication of the universal claim. Theorem 4.76 gives the biconditional over infinite fields.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.TDependent`
- Truth anchor: `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.TFull`
- Truth anchor: `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.TMap`
- Truth anchor: `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.TPrincipal`
- Truth anchor: `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.claim`
- Truth anchor: `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.delta`
- Truth anchor: `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.genericElement`
- Truth anchor: `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.genericImage`
- Truth anchor: `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.imageIdeal`
- Truth anchor: `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.result`
- Truth anchor: `D5/S3/HomologicalAlgebra/ShiYauZuoTPrincipalRefutation.valueIdeal`
