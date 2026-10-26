# Nontrivial product intersection spectra

## Abstract

Every infinite group admits a decreasing sequence with a nontrivial proper product intersection spectrum.

**Definition 1.1 (Asymptotically strict decrease).**

$$\forall (G : \operatorname{Type}), \forall (A : \mathbb{N}^{+} \to \operatorname{Set}\left(G\right)), \operatorname{ASD}\left(A\right) = ((\forall (q : \mathbb{N}^{+}), A\left(q + 1\right) \subseteq A\left(q\right)) \land (\operatorname{Set}.\operatorname{Infinite}\left(\{q : \mathbb{N}^{+} \mid A\left(q\right) \ne A\left(q + 1\right)\}\right)))$$

*Formalization.* `D5/S3/Combinatorics/GroupWords/NathansonProblem9.ASD` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *Problems and results on intersections of product sets and sumsets in semigroups*. DOI: [10.48550/arXiv.2604.04781](https://doi.org/10.48550/arXiv.2604.04781). URL: <https://arxiv.org/abs/2604.04781v2>.

*Commentary.*

Nathanson, Section 2, calls a sequence decreasing when every next set is contained in its predecessor, and asymptotically strictly decreasing when adjacent sets differ at infinitely many indices. The index type PNat is the positive integers. The common intersection may be empty.

**Definition 1.2 (The full positive spectrum).**

$$\forall (G : \operatorname{Type}), [\operatorname{Group}\left(G\right)], \forall (A : \mathbb{N}^{+} \to \operatorname{Set}\left(G\right)), \operatorname{spectrum}\left(A\right) = \{h : \mathbb{N} \mid (0 < h) \land ((\operatorname{Set}.\operatorname{iInter}\left(\operatorname{fun} (q : \mathbb{N}^{+}) \mapsto A\left(q\right)\right))^{h} = \operatorname{Set}.\operatorname{iInter}\left(\operatorname{fun} (q : \mathbb{N}^{+}) \mapsto (A\left(q\right))^{h}\right))\}$$

*Formalization.* `D5/S3/Combinatorics/GroupWords/NathansonProblem9.spectrum` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *Problems and results on intersections of product sets and sumsets in semigroups*. DOI: [10.48550/arXiv.2604.04781](https://doi.org/10.48550/arXiv.2604.04781). URL: <https://arxiv.org/abs/2604.04781v2>.

*Commentary.*

Section 1 defines the spectrum using equality between the power of the common intersection and the intersection of the powers. The natural exponent is restricted to be positive. Mathlib pointwise set powers are all ordered products of that many factors, with repetitions allowed. Multiplication need not commute.

**Theorem 1.3 (Existence in every infinite group).**

$$\forall (G : \operatorname{Type}), [\operatorname{Group}\left(G\right)], [\operatorname{Infinite}\left(G\right)], \exists (A : \mathbb{N}^{+} \to \operatorname{Set}\left(G\right)), (\operatorname{ASD}\left(A\right)) \land ((\operatorname{spectrum}\left(A\right) \ne \{1\}) \land (\operatorname{spectrum}\left(A\right) \ne \{h : \mathbb{N} \mid 0 < h\}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GroupWords/NathansonProblem9.result` (`✓ std3`). ∎

*Resolves.* `Problems/nathanson-2026-problem9-torsion-nontrivial-spectrum-existence` (proved) by `D5/S3/Combinatorics/GroupWords/NathansonProblem9.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nathanson-2026-problem9-torsion-nontrivial-spectrum-existence","declaration_gid":"D5/S3/Combinatorics/GroupWords/NathansonProblem9.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *Problems and results on intersections of product sets and sumsets in semigroups*. DOI: [10.48550/arXiv.2604.04781](https://doi.org/10.48550/arXiv.2604.04781). URL: <https://arxiv.org/abs/2604.04781v2>.

*Commentary.*

Problem 9 asks: “Let G be an infinite torsion group. Describe the product intersection sets H_Q(G). Must there exist X in H_N^*(G) with X != {1} and X != N?” The theorem answers the final existence question affirmatively. Set X equal to spectrum A; ASD A places X in H_N^*(G). The theorem applies to every infinite group, so the torsion hypothesis is unnecessary. G is arbitrary in cardinality and need not be abelian or have bounded exponent. The preceding classification request remains a separate question.

If the range of cubes is finite, an infinite common-cube fibre has injective squares: equality of squares together with equality of cubes cancels to equality of roots. Thin both ordered mixed pair products, and use singleton tails. Their common intersection and square-product intersection are empty, while the common cube lies in every cube-product set. Thus 2 belongs to the full spectrum and 3 does not.

If the range of cubes is infinite, recursively choose cubes outside all earlier cube inverse-orbits. The corresponding roots have pairwise disjoint inverse-pairs. Thin every signed mixed triple support. Pure signed triples take one of the four values x^3, x, inverse x, inverse(x^3), each of which eventually avoids any fixed group element. The inverse-pair tails have empty common intersection and empty cube-product intersection, while the identity belongs to every square-product set. Thus 3 belongs to the full spectrum and 2 does not.

The thinning uses Yann Pequignot's relativized all-arity infinite_ramsey at revision b63066fd9f8075a30bc78d392405426bf084e226. Its exists_infinite_fiber_nat supplies the final colour pigeonhole, and its Set.Infinite.exists_strictMono supplies increasing support enumeration. The compatible proof is preserved under Apache-2.0 with its complete license and attribution. A recursively chosen increasing diagonal handles countably many requirements. Only the initial word-evaluation range is countable; no countability assumption on G enters the argument.

The repository and its pinned Mathlib were searched for product-intersection spectra, infinite Ramsey thinning, cube ranges and the exact Nathanson question. The existing Problem 12 result concerns integer-additive affine invariance and supplies no group-existence theorem. At Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679, Finite.exists_infinite_fiber gives the common-cube fibre; Set.countable_range and countable_iff_exists_surjective enumerate the requirements; Nat.nth_strictMono and Nat.nth_mem_of_infinite enumerate infinite supports; Finset.orderEmbOfFin_unique identifies their increasing finite enumerations. Group cancellation and pointwise set powers supply the algebraic interfaces. The cited Ramsey source supplies the missing relativized all-arity theorem. The literature boundary is the bounded primary-source and prior-solution screen in the accompanying source note; no worldwide priority assertion follows.

## References

- Truth anchor: `D5/S3/Combinatorics/GroupWords/NathansonProblem9.ASD`
- Truth anchor: `D5/S3/Combinatorics/GroupWords/NathansonProblem9.result`
- Truth anchor: `D5/S3/Combinatorics/GroupWords/NathansonProblem9.spectrum`
