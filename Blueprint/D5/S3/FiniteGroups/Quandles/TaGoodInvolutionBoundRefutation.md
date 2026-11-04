# A quaternion subquandle attains the good-involution bound

## Abstract

The conjugation subquandle {±i, ±j} of the quaternion group Q8 has four good involutions and eight automorphisms. Its generated subgroup has center of order two and two conjugation orbits, so the bound min(8, 2^2) = 4 is attained. This answers Lực Ta's Problem 11.7 in the negative.

**Definition 1.1 (The strictness question).**

$$claim \Leftrightarrow (\forall (G : \operatorname{Type}) [\operatorname{Group}\left(G\right)] [\operatorname{Fintype}\left(G\right)] [\operatorname{DecidableEq}\left(G\right)], (\forall X : \operatorname{Finset}\left(G\right), (\forall h : \operatorname{ConjClosed}\left(X\right), ((2 \le \operatorname{NatCard}\left(\operatorname{center}\left(\operatorname{closure}\left((X : \operatorname{Set}\left(G\right))\right)\right)\right)) \Rightarrow ((2 \le \operatorname{orbitCount}\left(X\right)) \Rightarrow (\operatorname{FintypeCard}\left(\operatorname{Good}\left(X, h\right)\right) < \operatorname{min}\left(\operatorname{FintypeCard}\left(\operatorname{Aut}\left(X, h\right)\right), \operatorname{NatCard}\left(\operatorname{center}\left(\operatorname{closure}\left((X : \operatorname{Set}\left(G\right))\right)\right)\right)^{\operatorname{orbitCount}\left(X\right)}\right)))))))$$

*Formalization.* `D5/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation.claim` (`✓ std3`).

*Citation.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

Ta, Problem 11.7, printed page 27: "In the setting of Corollary 6.12, suppose that |Z(H)|, |X/H| ≥ 2 (so, in particular, Conj X is not connected). Is the upper bound on |Good(Conj X)| in Corollary 6.12 always strict?" Corollary 6.12, printed page 14: "Let k(X) := |X/H|. Then |Good(Conj X)| ≤ min(|Aut(Conj X)|, |Z(H)|^{k(X)}). If X is not closed under inverses, then the bound |Good(Conj X)| < |Z(H)|^{k(X)} is strict." The encoding quantifies over G : Type, each group structure, finite enumeration and decidable equality on G, every finite subset X, and every closure proof h. The binder names group, finite and eq denote these implicit Lean instances. DecidableEq is implementation structure, available classically. H = ⟨X⟩, k = orbitCount X, and z = Nat.card (Subgroup.center H); The displayed FintypeCard on Good and Aut is Fintype.card, NatCard is Nat.card, and FinsetCard is Finset.card. closure, center and Bijective denote Subgroup.closure, Subgroup.center and Function.Bijective, respectively. The displayed center cardinality and orbit count are expressions, rather than extra parameters. This is the finite-group strictness reading: a finite counterexample suffices to refute the unrestricted question. No assertion about infinite cardinal arithmetic is made.

**Theorem 1.2 (The bound is attained).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ta-2025-problem-11-7-good-involution-bound-refutation` (refuted) by `D5/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ta-2025-problem-11-7-good-involution-bound-refutation","declaration_gid":"D5/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lực Ta (2025). *Good involutions of conjugation subquandles*. DOI: [10.48550/arXiv.2505.08090](https://doi.org/10.48550/arXiv.2505.08090). URL: <https://arxiv.org/abs/2505.08090v5>.

*Commentary.*

Take G = QuaternionGroup 2 and X = {a 1, a 3, xa 0, xa 2} = {±i, ±j}. The inverse of a 1 is a 3 and the inverse of xa 0 is xa 2; a 1 and xa 0 do not commute. Conjugation preserves X, and a 1 and xa 0 generate G. The center has order two. The conjugation orbits are {a 1, a 3} and {xa 0, xa 2}, so k = 2. The four good involutions independently exchange or fix the two elements in each orbit. There are eight automorphisms. Thus |Good| = 4 = min(8, 2^2), which contradicts the proposed strict inequality.

## References

- Truth anchor: `D5/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation.claim`
- Truth anchor: `D5/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation.result`
- Dependency: [D5/S3/FiniteGroups/Quandles/ConjugationSubquandle](ConjugationSubquandle.md)
