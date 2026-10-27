# Finite generation for one-parameter polynomial invariants

## Abstract

Every family of rational univariate polynomials has a finite subfamily generating the same algebra.

**Definition 1.1 (A finite generating subfamily).**

$$(\operatorname{D5.S3.Topology.KnotFamilyVassilievFiniteGeneration.claim}: \operatorname{Prop}) = (\forall (\iota: \operatorname{Type}), (\forall (p: (\iota) \to (\operatorname{Polynomial}\left(\mathbb{Q}\right))), (\exists (s: \operatorname{Finset}\left(\iota\right)), (\operatorname{Algebra.adjoin}\left(\mathbb{Q}, \operatorname{Set.image}\left(p, (s: \operatorname{Set}\left(\iota\right))\right)\right) = \operatorname{Algebra.adjoin}\left(\mathbb{Q}, \operatorname{Set.range}\left(p\right)\right)))))$$

*Formalization.* `D5/S3/Topology/KnotFamilyVassilievFiniteGeneration.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* E. Lanina; A. Sleptsov (2026). *Algebraic structures of Vassiliev invariants for knot families*. DOI: [10.1016/j.nuclphysb.2025.117268](https://doi.org/10.1016/j.nuclphysb.2025.117268). URL: <https://arxiv.org/abs/2508.02385v2>.

*Commentary.*

The family p is indexed by an arbitrary type ι and consists of polynomials over the rational numbers. The assertion asks for a finite set s of indices whose polynomial values generate the same rational subalgebra as the entire family. The expression (s : Set ι) explicitly regards the finite set as a set before taking its image under p. Lanina–Sleptsov describe rational-valued invariants and their algebra in main.tex, lines 350–356, write the one-parameter restrictions as rational polynomials in lines 1114–1117, and ask for finite generation in lines 165 and 1166. Taking p to be these polynomial restrictions gives the algebraic assertion. Generation is ordinary algebra generation: the twist-knot discussion in line 1228 allows higher-order invariants to be polynomials in the second invariant. There is no requirement that the generators preserve the order filtration.

**Theorem 1.2 (Subalgebras of a polynomial ring in one variable).**

$$\forall (k: \operatorname{Type}*), ([\operatorname{Field}\left(k\right)], \forall (a: \operatorname{Subalgebra}\left(k, \operatorname{Polynomial}\left(k\right)\right)), (\operatorname{Subalgebra.FG}\left(a\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/KnotFamilyVassilievFiniteGeneration.subalgebra_fg` (`✓ std3`). ∎

*Citation.* Emil Artin; John T. Tate (1951). *A Note on Finite Ring Extensions*. DOI: [10.2969/jmsj/00310074](https://doi.org/10.2969/jmsj/00310074). URL: <https://stacks.math.columbia.edu/tag/00IS>.

*Commentary.*

For every field k, each k-subalgebra a of the polynomial ring k[X] is finitely generated as a k-algebra. Subalgebra.FG means that a finite set of polynomials generates a as a subalgebra. This is the standard finiteness fact, proved here from the integrality of X over k[f] for a nonconstant polynomial f and the Artin–Tate lemma. For a containing f, the same monic polynomial proves integrality over a; when a contains only constants it is the scalar subalgebra.

**Theorem 1.3 (Finite generation by members of the given family).**

$$\forall (\iota: \operatorname{Type}), (\forall (p: (\iota) \to (\operatorname{Polynomial}\left(\mathbb{Q}\right))), (\exists (s: \operatorname{Finset}\left(\iota\right)), (\operatorname{Algebra.adjoin}\left(\mathbb{Q}, \operatorname{Set.image}\left(p, (s: \operatorname{Set}\left(\iota\right))\right)\right) = \operatorname{Algebra.adjoin}\left(\mathbb{Q}, \operatorname{Set.range}\left(p\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/KnotFamilyVassilievFiniteGeneration.result` (`✓ std3`). ∎

*Resolves.* `Problems/lanina-sleptsov-2026-vassiliev-one-parameter-finite-generation` (proved) by `D5/S3/Topology/KnotFamilyVassilievFiniteGeneration.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lanina-sleptsov-2026-vassiliev-one-parameter-finite-generation","declaration_gid":"D5/S3/Topology/KnotFamilyVassilievFiniteGeneration.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* E. Lanina; A. Sleptsov (2026). *Algebraic structures of Vassiliev invariants for knot families*. DOI: [10.1016/j.nuclphysb.2025.117268](https://doi.org/10.1016/j.nuclphysb.2025.117268). URL: <https://arxiv.org/abs/2508.02385v2>.

*Commentary.*

First consider an arbitrary k-subalgebra a of k[X]. If every f in a has natural degree zero, each is the constant polynomial with value its zeroth coefficient. Thus a is contained in the scalar subalgebra; the reverse inclusion holds for every k-subalgebra. Equality with the scalar subalgebra gives finite generation by the empty set.

Otherwise choose f in a of positive natural degree and let c be its nonzero leading coefficient. The polynomial q = C(c⁻¹)f is monic and still has positive natural degree. Map its coefficients along the scalar homomorphism from k to a. The resulting polynomial over a remains monic of positive degree, and its evaluation at X is the image under a → k[X] of the element q of a, since a contains both f and the scalar C(c⁻¹). This evaluated value is integral over a. The monic evaluation criterion therefore makes X integral over a; equivalently, subtracting that value from the constant coefficient gives a monic polynomial vanishing at X.

The a-subalgebra generated by X is all of k[X]: after restricting scalars to k, it contains X, which generates k[X] over k. Since X is integral, the subalgebra it generates is a finite a-module, so k[X] is a finite a-module. Apply the Artin–Tate lemma to the tower k → a → k[X], using that the field k is Noetherian, that k[X] is a finitely generated k-algebra, and that the inclusion of a is injective. It follows that a is a finitely generated k-algebra. The preceding two cases prove the general subalgebra finiteness statement.

Next let p be a polynomial family. An induction on membership in the algebra generated by its range shows that every element belongs to the algebra generated by a finite subfamily. An original value p(i) uses the singleton index set containing i, and a scalar uses the empty index set. For a sum or product, take the union of the two finite index sets and use monotonicity of generated subalgebras.

Choose a finite set t of polynomial generators for the algebra generated by the range of p. For each x in t choose a finite index set s(x) whose values generate a subalgebra containing x. Take the finite union of s(x) over x in t. Its polynomial values lie in the range of p, giving one inclusion of generated algebras. Conversely, every generator x in t belongs to the algebra generated by that union, giving the other inclusion. Finally specialize to k equal to the rational field and apply the general subalgebra finiteness statement to the algebra generated by the range of p. The resulting finite set of indices proves the assertion for every ι and p.

## References

- Truth anchor: `D5/S3/Topology/KnotFamilyVassilievFiniteGeneration.claim`
- Truth anchor: `D5/S3/Topology/KnotFamilyVassilievFiniteGeneration.result`
- Truth anchor: `D5/S3/Topology/KnotFamilyVassilievFiniteGeneration.subalgebra_fg`
