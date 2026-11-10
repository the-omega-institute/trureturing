# Tutte linking for finite native matroids

## Abstract

A finite matroid has a minor on the two terminal sets that realizes their minimum separating-cut connectivity.

**Theorem 1.1 (An actual terminal minor attaining the cut minimum).**

$$\forall (E: Type_{u}), [Finite\left(E\right)] \forall (M: Matroid\left(E\right)), \forall (S: Set\left(E\right)), \forall (T: Set\left(E\right)), (S \subseteq \operatorname{Matroid}.\operatorname{E}\left(M\right)) \Rightarrow ((T \subseteq \operatorname{Matroid}.\operatorname{E}\left(M\right)) \Rightarrow ((Disjoint\left(S, T\right)) \Rightarrow (\exists (C: Set\left(E\right)), (C \subseteq (\operatorname{Matroid}.\operatorname{E}\left(M\right)) \setminus ((S) \cup (T))) \land (let D: Set\left(E\right) := ((\operatorname{Matroid}.\operatorname{E}\left(M\right)) \setminus ((S) \cup (T))) \setminus (C); let N: Matroid\left(E\right) := \operatorname{Matroid}.\operatorname{delete}\left(\operatorname{Matroid}.\operatorname{contract}\left(M, C\right), D\right); (\operatorname{Matroid}.\operatorname{E}\left(N\right) = (S) \cup (T)) \land (\operatorname{TutteLinking}.\operatorname{rk}\left(N, S\right) + \operatorname{TutteLinking}.\operatorname{rk}\left(N, T\right) - \operatorname{TutteLinking}.\operatorname{rk}\left(N, ((S) \cup (T))\right) = \operatorname{TutteLinking}.\operatorname{kappa}\left(M, S, T\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/TutteLinking.tutte_linking` (`✓ std3`). ∎

*Citation.* Henning Bruhn; Paul Wollan (2011). *Finite connectivity in infinite matroids*. URL: <https://arxiv.org/abs/1101.5621v1>.

*Commentary.*

Let E : Type u be any finite type in any universe u, and let M be any native Matroid E. Let S and T be disjoint subsets of M.E. Define rk M X = ENat.toNat (M.eRk X), cut M X = rk M X + rk M (M.E minus X) - rk M M.E, and kappa M S T to be the natural-number infimum of all cut M X with S contained in X and X contained in M.E minus T. The complement is always relative to the ground of the matroid appearing in that cut.

There exists a set C contained in M.E minus (S union T). Put D = (M.E minus (S union T)) minus C and N = (M / C) minus D, using native matroid contraction and deletion. Then N.E equals S union T, and rk N S + rk N T - rk N (S union T) equals kappa M S T. Thus C and D partition exactly the nonterminal ground, and the conclusion supplies an actual minor. On this terminal ground the sole feasible separating cut is S, so its terminal rank defect is also its minimum separating-cut connectivity.

Finiteness of E makes every native rank used here finite; ENat.toNat therefore preserves rank values and addition. Rank subadditivity makes both displayed rank defects nonnegative before natural subtraction. Empty terminals, empty ground, loops, coloops and rank zero are included. There is no representability, positive-connectivity or nonempty-terminal assumption, and no optimum, certificate or minor is supplied as a premise.

For the construction, put R = M.E minus (S union T), A = (M / S) minus T and B = (M / T) minus S. Both matroids have ground R. Finite matroid intersection supplies a single common independent set I and an attaining rank cut X. Its universal upper bound makes I maximum in cardinality. If an element of M.E lay outside the closure of S union T union I, adjoining it to I would remain independent in both A and B, contradicting that upper bound. Consequently S union T union I spans M.

Take C = I. Independence in M / S and M / T implies rk M (S union I) = rk M S + I.ncard and rk M (T union I) = rk M T + I.ncard. Independence in M gives rk M I = I.ncard. The contraction rank identity and deletion of only nonterminals then give rk N S = rk M S, rk N T = rk M T and rk N (S union T) + I.ncard = rk M M.E. These identities express the terminal rank defect in terms of the same intersection certificate.

The attaining intersection cut X yields the feasible original cut S union X; its complement is (R minus X) union T. The two contraction rank identities show that its connectivity equals the terminal rank defect. For every other feasible original cut Y, apply the common-independent upper bound to Y minus S. Its complementary side in R, together with T, is M.E minus Y. The same rank identities show that the terminal rank defect is at most cut M Y. The feasible cut family is nonempty, its minimum is attained by S union X, and the infimum is exactly the asserted minor value.

Bruhn and Wollan, arXiv:1101.5621v1, pages 1–2, define the finite rank connectivity and the minimum over separating cuts and state this classical partition theorem as Theorem 1, attributed to Tutte. The finite intersection theorem is reused from FiniteIntersection.finite_matroid_intersection; the contraction rank identity is FiniteIntersection.contract_eRk_add. The construction applies to all finite native matroids, including nonrepresentable ones.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/TutteLinking.tutte_linking`
- Dependency: [D5/S3/Combinatorics/Matroids/FiniteIntersection](FiniteIntersection.md)
