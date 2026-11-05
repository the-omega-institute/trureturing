# An obstruction to diagonal spinor Poisson brackets

## Abstract

Jacobi and reducedness rule out the proposed diagonal spinor Poisson brackets for the second E6 and truck families.

**Definition 1.1 (A complex Poisson bracket).**

$$\forall (R: \operatorname{Type}*), ([\operatorname{CommRing}\left(R\right)], ([\operatorname{Algebra}\left(\mathbb{C}, R\right)], (\forall (br: (R) \to ((R) \to (R))), ((\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.IsPoissonBracket}\left(br\right)) \Leftrightarrow ((\forall (a: R), (\forall (b: R), (\forall (c: R), (br\left((a) + (b), c\right) = (br\left(a, c\right)) + (br\left(b, c\right)))))) \land ((\forall (c: \mathbb{C}), (\forall (a: R), (\forall (b: R), (br\left((c) \cdot (a), b\right) = (c) \cdot (br\left(a, b\right)))))) \land ((\forall (a: R), (\forall (b: R), (\forall (c: R), (br\left(a, (b) + (c)\right) = (br\left(a, b\right)) + (br\left(a, c\right)))))) \land ((\forall (c: \mathbb{C}), (\forall (a: R), (\forall (b: R), (br\left(a, (c) \cdot (b)\right) = (c) \cdot (br\left(a, b\right)))))) \land ((\forall (a: R), (\forall (b: R), (br\left(a, b\right) = -(br\left(b, a\right))))) \land ((\forall (a: R), (\forall (b: R), (\forall (c: R), (br\left(a, (b) \cdot (c)\right) = ((br\left(a, b\right)) \cdot (c)) + ((b) \cdot (br\left(a, c\right))))))) \land (\forall (a: R), (\forall (b: R), (\forall (c: R), (((br\left(a, br\left(b, c\right)\right)) + (br\left(b, br\left(c, a\right)\right))) + (br\left(c, br\left(a, b\right)\right)) = (0: R)))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.IsPoissonBracket` (`✓ std3`).

*Citation.* Kirsty Gledhill; Amihay Hanany (2023). *Poisson brackets for some Coulomb branches*. DOI: [10.1007/JHEP03(2023)154](https://doi.org/10.1007/JHEP03(2023)154). URL: <https://arxiv.org/abs/2210.02966v2>.

*Commentary.*

For a commutative complex algebra R, br is additive and complex homogeneous in each argument, antisymmetric, a derivation in its second argument, and satisfies the cyclic Jacobi identity. Antisymmetry also gives the derivation rule in the first argument. These are the Poisson axioms in Gledhill–Hanany, arXiv:2210.02966v2, main.tex, line 2237.

**Definition 1.2 (The diagonal spinor relations).**

$$\forall (R: \operatorname{Type}*), ([\operatorname{CommRing}\left(R\right)], (\forall (N: \mathbb{N}), (\forall (br: (R) \to ((R) \to (R))), (\forall (h: R), (\forall (sUp: (\operatorname{Fin}\left(N\right)) \to (R)), (\forall (sDn: (\operatorname{Fin}\left(N\right)) \to (R)), (\forall (e: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.SpinorBrackets}\left(br, h, sUp, sDn, e\right)) \Leftrightarrow ((\forall (\alpha: \operatorname{Fin}\left(N\right)), (br\left(h, sUp\left(\alpha\right)\right) = sUp\left(\alpha\right))) \land ((\forall (\alpha: \operatorname{Fin}\left(N\right)), (br\left(h, sDn\left(\alpha\right)\right) = -(sDn\left(\alpha\right)))) \land ((\forall (\alpha: \operatorname{Fin}\left(N\right)), (\forall (\beta: \operatorname{Fin}\left(N\right)), (br\left(sUp\left(\alpha\right), sDn\left(\beta\right)\right) = \operatorname{ite}\left(\alpha = \beta, (h)^{e}, (0: R)\right)))) \land ((\forall (\alpha: \operatorname{Fin}\left(N\right)), (\forall (\beta: \operatorname{Fin}\left(N\right)), (br\left(sUp\left(\alpha\right), sUp\left(\beta\right)\right) = (0: R)))) \land (\forall (\alpha: \operatorname{Fin}\left(N\right)), (\forall (\beta: \operatorname{Fin}\left(N\right)), (br\left(sDn\left(\alpha\right), sDn\left(\beta\right)\right) = (0: R))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.SpinorBrackets` (`✓ std3`).

*Citation.* Kirsty Gledhill; Amihay Hanany (2023). *Poisson brackets for some Coulomb branches*. DOI: [10.1007/JHEP03(2023)154](https://doi.org/10.1007/JHEP03(2023)154). URL: <https://arxiv.org/abs/2210.02966v2>.

*Commentary.*

The functions sUp and sDn give N components of weights plus one and minus one under br h. A mixed bracket equals h to the natural power e on the diagonal and zero off the diagonal; brackets between components of the same charge vanish. The conditional expression is the Kronecker delta rule. These are the spinor relations and the unlisted vanishing brackets of main.tex, lines 1851–1856 and 2191–2197. No positivity of e or lower bound on N is imposed by this definition.

**Definition 1.3 (The second E6 family).**

$$(\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.ConjE6}) \Leftrightarrow (\forall (n: \mathbb{N}), ((3 \le n) \Rightarrow (\exists (R: \operatorname{Type}), (\exists (ringR: \operatorname{CommRing}\left(R\right)), (\operatorname{letI} := ringR; (\exists (algR: \operatorname{Algebra}\left(\mathbb{C}, R\right)), (\operatorname{letI} := algR; ((\operatorname{IsReduced}\left(R\right)) \land (\exists (br: (R) \to ((R) \to (R))), (\exists (h: R), (\exists (sUp: (\operatorname{Fin}\left((2)^{(2) \cdot (n)}\right)) \to (R)), (\exists (sDn: (\operatorname{Fin}\left((2)^{(2) \cdot (n)}\right)) \to (R)), ((\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.IsPoissonBracket}\left(br\right)) \land ((h \ne (0: R)) \land (\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.SpinorBrackets}\left(br, h, sUp, sDn, (n) - (1)\right))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.ConjE6` (`✓ std3`).

*Citation.* Kirsty Gledhill; Amihay Hanany (2023). *Poisson brackets for some Coulomb branches*. DOI: [10.1007/JHEP03(2023)154](https://doi.org/10.1007/JHEP03(2023)154). URL: <https://arxiv.org/abs/2210.02966v2>.

*Commentary.*

For every natural n at least three, the proposed spinor relations are required in a reduced commutative complex algebra, with h nonzero, two spinor families of dimension two to the power 2n, and exponent n minus one. The two algebraic structures are chosen along with R. The symbol letI indicates that the chosen structure is used in the following expression. The source gives this rank range at main.tex, line 1807, the spinor dimension at line 1843, and the bracket conjecture at lines 1845–1856. The formula retains the spinor conditions on a reduced coordinate algebra and omits the additional adjoint generators.

**Definition 1.4 (The truck family).**

$$(\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.ConjTruck}) \Leftrightarrow (\forall (n: \mathbb{N}), ((2 \le n) \Rightarrow (\forall (\sigma: \mathbb{N}), ((1 \le \sigma) \Rightarrow (\exists (R: \operatorname{Type}), (\exists (ringR: \operatorname{CommRing}\left(R\right)), (\operatorname{letI} := ringR; (\exists (algR: \operatorname{Algebra}\left(\mathbb{C}, R\right)), (\operatorname{letI} := algR; ((\operatorname{IsReduced}\left(R\right)) \land (\exists (br: (R) \to ((R) \to (R))), (\exists (h: R), (\exists (sUp: (\operatorname{Fin}\left((2)^{(2) \cdot (n)}\right)) \to (R)), (\exists (sDn: (\operatorname{Fin}\left((2)^{(2) \cdot (n)}\right)) \to (R)), ((\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.IsPoissonBracket}\left(br\right)) \land ((h \ne (0: R)) \land (\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.SpinorBrackets}\left(br, h, sUp, sDn, ((n) + (\sigma)) - (1)\right))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.ConjTruck` (`✓ std3`).

*Citation.* Kirsty Gledhill; Amihay Hanany (2023). *Poisson brackets for some Coulomb branches*. DOI: [10.1007/JHEP03(2023)154](https://doi.org/10.1007/JHEP03(2023)154). URL: <https://arxiv.org/abs/2210.02966v2>.

*Commentary.*

For every natural n at least two and every positive natural multiplicity σ, a reduced commutative complex algebra is required with the same nonzero weight element and spinor dimension, now with exponent n plus σ minus one. Subtraction in both family definitions is natural subtraction. The quiver range is given at main.tex, line 2149, and the spinor dimension and bracket conjecture at lines 2185–2197. Only the spinor consequences are imposed here.

**Definition 1.5 (Existence of at least one proposed family).**

$$(\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.claim}) \Leftrightarrow ((\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.ConjE6}) \lor (\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.ConjTruck}))$$

*Formalization.* `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kirsty Gledhill; Amihay Hanany (2023). *Poisson brackets for some Coulomb branches*. DOI: [10.1007/JHEP03(2023)154](https://doi.org/10.1007/JHEP03(2023)154). URL: <https://arxiv.org/abs/2210.02966v2>.

*Commentary.*

The proposition is the disjunction of the two universally quantified family statements. Thus it asserts the existence of all the required algebras for at least one family, with the algebra and bracket allowed to depend on the family parameters. It expresses necessary spinor conditions for the source's conjectures; it asserts neither the adjoint relations nor an identification of an arbitrary algebra satisfying them with a Coulomb branch.

**Theorem 1.6 (Neither proposed family exists).**

$$\neg (\operatorname{D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gledhill-hanany-2023-coulomb-branch-poisson-bracket-refutation` (refuted) by `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gledhill-hanany-2023-coulomb-branch-poisson-bracket-refutation","declaration_gid":"D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kirsty Gledhill; Amihay Hanany (2023). *Poisson brackets for some Coulomb branches*. DOI: [10.1007/JHEP03(2023)154](https://doi.org/10.1007/JHEP03(2023)154). URL: <https://arxiv.org/abs/2210.02966v2>.

*Commentary.*

Fix a complex Poisson bracket on a reduced commutative complex algebra R. For each a, the map b ↦ br a b is a complex derivation, so it vanishes at zero and obeys the usual power rule. Antisymmetry and the right Leibniz rule give br (a*b) c = a*(br b c) + (br a c)*b.

Suppose e is at least one and h, x, y, z, w satisfy br h x = x, br h y = −y, br x y = br z w = h^e, and br x w = br x z = 0. Write e = k+1. Antisymmetry gives br w x = 0 and br x h = −x. Jacobi on x, z, w then reduces to the power rule for br x (h^(k+1)). It gives the vanishing of the complex scalar k+1 times h^k*x. The scalar is explicitly the natural number k+1 cast to the complex numbers, and is nonzero. Cancelling it yields h^k*x = 0.

Consequently br (h^k*x) y = 0. Expanding by the left Leibniz rule, substituting br x y = h^(k+1), and using antisymmetry and the power rule on br y (h^k) gives $(((h)^{k}) \cdot ((h)^{(k) + (1)})) + ((-\left(((\operatorname{Nat.cast}\left(k\right): R)) \cdot (((h)^{(k) - (1)}) \cdot (y))\right)) \cdot (x)) = (0: R)$. Here k is cast from the natural numbers to R, and k−1 is natural subtraction. Multiplying the correction term by h makes it zero: at k=0 its scalar coefficient is zero, while at k=m+1 it becomes the natural number m+1 cast to R times h^(m+1)*x*y, which vanishes by h^k*x = 0. Multiplying the expanded bracket identity by h and rearranging therefore gives h^(2*(k+1)) = 0. Reducedness makes every nilpotent element zero, so h = 0.

For spinor relations with N at least two, choose the distinct indices i=0 and j=1 in Fin N, and put x=sUp i, y=sDn i, z=sUp j, w=sDn j. The weight relations give br h x = x and br h y = −y. The two diagonal mixed brackets give br x y = br z w = h^e; the off-diagonal mixed bracket and the equal-charge bracket give br x w = br x z = 0. Thus every such collection with e at least one forces h = 0.

Apply the second E6 family statement at n=3: N=2^6=64 and e=2. The preceding argument gives h = 0, contrary to its required nonvanishing. Apply the truck family statement at n=2 and σ=1: N=2^4=16 and e=2, giving the same contradiction. Each side of the disjunction is therefore impossible, proving its negation. The obstruction concerns precisely the displayed normalized mixed brackets together with the vanishing equal-charge brackets in a reduced complex algebra; it does not require any adjoint-generator relations.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.ConjE6`
- Truth anchor: `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.ConjTruck`
- Truth anchor: `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.IsPoissonBracket`
- Truth anchor: `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.SpinorBrackets`
- Truth anchor: `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.result`
