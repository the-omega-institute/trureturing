# Ordinary generation need not produce a compatible pair

## Abstract

On Q8, ordinary generation after adding the bottom-to-top arrow fails the compatibility clause of Conjecture 4.2.

**Definition 1.1 (The full universal conjecture).**

$$\operatorname{claim} : \operatorname{Prop} = \forall (G : \operatorname{Type}) [\operatorname{Group}\left(G\right)] [\operatorname{Finite}\left(G\right)] , (\forall T : \operatorname{TransferSystem}\left(G\right), ((\operatorname{TwoComponents}\left(T\right)) \Rightarrow ((\operatorname{TopIsolated}\left(T\right)) \Rightarrow ((\neg \operatorname{LesserSimplyPaired}\left(T\right)) \land (\operatorname{Compatible}\left(T, \operatorname{generated}\left(T\right)\right))))))$$

*Formalization.* `D5/S3/FiniteGroups/KlandermanConjecture42Refutation.claim` (`✓ std3`).

*Citation.* Sarah Klanderman, Chloe Lewis, Harlea Monson, Koki Shibata and Danika Van Niel (2025). *Characterizing Transfer Systems for Non-Abelian Groups*. DOI: [10.48550/arXiv.2511.13439](https://doi.org/10.48550/arXiv.2511.13439). URL: <https://arxiv.org/abs/2511.13439v2>.

*Commentary.*

Conjecture 4.2 of Klanderman, Lewis, Monson, Shibata and Van Niel, arXiv:2511.13439v2, printed page 15, asserts both non-LSP and compatibility. The claim quantifies over every finite group and every transfer system on all its actual subgroups. No saturation, non-abelian restriction, bound on the carrier, or selected list of subgroups is assumed. Group and Finite are anonymous Lean instance arguments.

TransferSystem records refinement of subgroup inclusion, reflexivity, composition, restriction and conjugation. Refinement gives antisymmetry. For L ≤ H, H ∩ L = L, so its restriction field with target L is precisely Definition 2.1. Conjugation is Subgroup.map under Mathlib's MulAut.conj g, hence sends K to gKg⁻¹.

Compatible(T,U) means that T is contained in U and, for all actual subgroups B,C ≤ A, T(B,A) and U(B ∩ C,B) imply U(C,A). This is the order (T₁,T₂) of Definition 2.14. Saturated means that L ≤ K ≤ H and T(L,H) imply T(K,H). The hull relation is the intersection of all saturated transfer extensions of T. This family contains the complete inclusion relation; intersections preserve all transfer axioms and saturation, contain T, and are contained in every member. Thus it is the source's least saturated hull. LesserSimplyPaired requires every compatible U to equal that hull or the complete inclusion relation; equality is expressed by agreement on every pair of subgroups.

arrowGraph is the actual SimpleGraph on Subgroup G, with an undirected edge between distinct K,H whenever T(K,H) or T(H,K). Removing identity loops changes no component. TwoComponents requires the components of the trivial and whole subgroups to be distinct and every SimpleGraph.ConnectedComponent to equal one of them. TopIsolated says every arrow incident to the whole group is its identity. Under reflexivity, this is equivalent to the conjecture's assertion that its component has only G → G.

**Definition 1.2 (The least ordinary transfer extension).**

$$\forall (G : \operatorname{Type}) [\operatorname{Group}\left(G\right)] , (\forall T : \operatorname{TransferSystem}\left(G\right), (\forall K : \operatorname{Subgroup}\left(G\right), (\forall H : \operatorname{Subgroup}\left(G\right), (\operatorname{rel}\left(\operatorname{generated}\left(T\right), K, H\right) \Leftrightarrow (\forall U : \operatorname{TransferSystem}\left(G\right), ((\operatorname{Extends}\left(T, U\right)) \Rightarrow ((\operatorname{rel}\left(U, \operatorname{bot}, \operatorname{top}\right)) \Rightarrow (\operatorname{rel}\left(U, K, H\right)))))))))$$

*Formalization.* `D5/S3/FiniteGroups/KlandermanConjecture42Refutation.generated` (`✓ std3`).

*Citation.* Sarah Klanderman, Chloe Lewis, Harlea Monson, Koki Shibata and Danika Van Niel (2025). *Characterizing Transfer Systems for Non-Abelian Groups*. DOI: [10.48550/arXiv.2511.13439](https://doi.org/10.48550/arXiv.2511.13439). URL: <https://arxiv.org/abs/2511.13439v2>.

*Commentary.*

Here rel(U,K,H) denotes U.rel K H, bot is the trivial subgroup and top is the whole group. For each T, generated T intersects all ordinary transfer systems U containing T and bot → top. The complete system belongs to this family, and the definition supplies every transfer axiom. Each arrow of T and bot → top belongs to every U, so both are included. Conversely, if U contains these generators, evaluating the displayed universal quantifier at U proves generated T ⊆ U. This is exactly ordinary least generation. The source cites Rubin's Construction A.1; his Theorem A.2 identifies the construction by this leastness property. No compatibility or saturation closure is part of generated.

**Theorem 1.3 (The quaternion witness).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/KlandermanConjecture42Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/klanderman-2025-conjecture-4-2` (refuted) by `D5/S3/FiniteGroups/KlandermanConjecture42Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"klanderman-2025-conjecture-4-2","declaration_gid":"D5/S3/FiniteGroups/KlandermanConjecture42Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sarah Klanderman, Chloe Lewis, Harlea Monson, Koki Shibata and Danika Van Niel (2025). *Characterizing Transfer Systems for Non-Abelian Groups*. DOI: [10.48550/arXiv.2511.13439](https://doi.org/10.48550/arXiv.2511.13439). URL: <https://arxiv.org/abs/2511.13439v2>.

*Commentary.*

Take the existing Mathlib group Q8 = QuaternionGroup 2. Set Z = zpowers(a 2) and A = zpowers(a 1), so bot < Z < A < top. The element a 2 is nonidentity. It is the square of a 1, while a 1 is absent from the two-element cyclic subgroup Z. Every power of a 1 is of constructor a, so xa 0 is absent from A. These facts establish the strict chain without enumerating or replacing the subgroup lattice.

Define T(K,H) by K = H or (K = bot and H ≠ top). All nonidentity arrows have source bot. Refinement and reflexivity follow immediately. In a composite the first arrow is an identity or has source bot; the second arrow either preserves its proper target or again has proper target. Restriction has source bot ∩ L = bot and a proper target L ≤ H < top. Conjugation fixes bot and preserves properness because it is a group automorphism. Thus T satisfies every source transfer axiom.

Every proper subgroup distinct from bot is adjacent to bot. No nonidentity arrow meets top. Its neighbor set is empty, and Mathlib's reachability criterion separates its actual connected component from that of bot. Induction over actual connected components then shows that these are all components. The hypotheses of the conjecture hold for T.

Let U(K,H) mean K = H or K = bot. It also satisfies all five transfer axioms and contains T and bot → top. Leastness gives generated T ⊆ U. Conversely, identities belong to generated T, and restriction of bot → top along every H gives bot → H. These are all arrows of U. The private generated_star proof therefore identifies the ordinary generated relation with U on every actual pair K,H, without a compatibility step.

Apply the asserted compatibility at ambient A, B = bot and C = Z. The arrow bot → A belongs to T since A is proper; bot ∩ Z → bot is the identity in generated T. Compatibility would force Z → A. The exact generated-system identification says that this requires Z = A or Z = bot, contradicting the two strict inclusions. This refutes the full conjunction through its compatibility clause. It does not assert the falsity of the non-LSP clause or resolve it separately.

## References

- Truth anchor: `D5/S3/FiniteGroups/KlandermanConjecture42Refutation.claim`
- Truth anchor: `D5/S3/FiniteGroups/KlandermanConjecture42Refutation.generated`
- Truth anchor: `D5/S3/FiniteGroups/KlandermanConjecture42Refutation.result`
