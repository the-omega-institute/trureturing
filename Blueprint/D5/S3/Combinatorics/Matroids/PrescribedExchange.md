# Rank-bounded simultaneous prescribed exchange

## Abstract

Prescriptions in opposite base differences extend to one simultaneous exchange bounded by their union rank.

**Theorem 1.1 (Prescribed exchange for arbitrary finite native matroids).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M: \operatorname{Matroid}\left(E\right)), (\forall (A: \operatorname{Set}\left(E\right)), (\forall (B: \operatorname{Set}\left(E\right)), (\forall (X: \operatorname{Set}\left(E\right)), (\forall (Y: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, A\right)) \Rightarrow ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, B\right)) \Rightarrow ((X \subseteq (A \setminus B)) \Rightarrow ((Y \subseteq (B \setminus A)) \Rightarrow (\exists (U: \operatorname{Set}\left(E\right)), (\exists (V: \operatorname{Set}\left(E\right)), ((U \subseteq (A \setminus B)) \land ((V \subseteq (B \setminus A)) \land ((X \subseteq U) \land ((Y \subseteq V) \land ((\operatorname{Set}.\operatorname{ncard}\left(U\right) = \operatorname{Set}.\operatorname{ncard}\left(V\right)) \land ((\operatorname{Set}.\operatorname{ncard}\left(U\right) \le \operatorname{ENat}.\operatorname{toNat}\left(\operatorname{Matroid}.\operatorname{eRk}\left(M, \operatorname{Set}.\operatorname{union}\left(X, Y\right)\right)\right)) \land ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, \operatorname{Set}.\operatorname{union}\left((A \setminus U), V\right)\right)) \land (\operatorname{Matroid}.\operatorname{IsBase}\left(M, \operatorname{Set}.\operatorname{union}\left((B \setminus V), U\right)\right))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PrescribedExchange.exists_prescribed_exchange` (`✓ std3`). ∎

*Citation.* Taihei Oki and Tamás Schwarcz (2025). *Generalizing the Multiple Exchange Property for Matroid Bases*. URL: <https://arxiv.org/abs/2511.16021v3>.

*Commentary.*

Let E be a finite type in an arbitrary universe, M a native matroid on E, and A and B bases of M. For each prescribed subset X of A minus B and each prescribed subset Y of B minus A, one pair U,V extends both prescriptions inside the respective base differences. The two sets have equal cardinality, bounded by the native rank of X union Y. Removing U from A and adding V gives a base, and removing V from B and adding U also gives a base. Both base conclusions hold for this same pair.

Cardinality is Set.ncard and rank is ENat.toNat of Matroid.eRk. Finiteness of the ambient type makes these ranks finite. Empty carriers, proper or empty native grounds, empty prescriptions, rank zero, intersecting or coincident bases, loops, coloops and nonrepresentable matroids are included. The statement is an existence theorem and asserts no algorithmic complexity.

Contract the intersection of the bases and restrict to their union minus that intersection. The resulting bases partition the resulting native ground. Contract X and delete Y in this matroid and in its dual. The base A minus X is common to these two residual minors. Integral weight splitting for the indicator of A minus X produces a single common base C and integral summands c,d for which C is separately minimum in both minors.

For each integer threshold t, let S(t) contain residual elements with c-weight at most t, and let H(t) be the union of A intersect S(t) and B intersect S(t-1). Integrality and the indicator split identify the complement of H(t) with the d-threshold at minus t. Minimum-base threshold saturation therefore supplies both coupled rank profiles. Two applications of submodularity, together with independence inside A and B, bound the rank increase from S(t-1) to S(t) by the increase in the cardinality of B intersect C intersect S(t).

Finite lower and upper bounds on the c-weights allow the paired inequality to telescope from the empty threshold to the whole residual ground, including an empty residual ground. The resulting inequality bounds the cardinality of A intersect C plus the cardinality of X by the rank of X union Y. Take U to be the union of A intersect C with X and take V to be B minus C. The common residual base gives both exchanged bases and equal exchange cardinalities. Lifting through restriction and contraction gives both original bases; contraction rank monotonicity gives the stated bound in the original matroid.

This is the existence assertion of Oki and Schwarcz, Theorem 1.6(i). The rank argument is the paired threshold form of Section 3.1. Theorem 1.6(ii), concerning independence-oracle queries, is a separate assertion.

Application: robustness of local search. Oki–Schwarcz, arXiv:2511.16021v3, Theorem 1.7 and Lemma 4.1, Section 4, printed pages 19–20, give the following consequence of simultaneous exchange. The derivation below applies the existing PrescribedExchange.exists_prescribed_exchange, finite attained-extremum facts and ordinary base exchange. It is application exposition within this theorem's commentary, with no separate Lean declaration or exact theorem anchor for the application.

Fix any universe u, finite ambient type E : Type u, native matroid M on E and arbitrary signed weight w : E -> R. All bases below are bases of this same M, represented as subsets of E, or equivalently as {D : Set E // M.IsBase D}. Write W(D) for NativeWeightedBaseRankSaturation.baseWeight w D, the finite sum of w over D. For natural t, let N_t(B) be the actual radius-t neighborhood and H_t(B) its attained maximum weight:

$$
\left(N_{t}\right)\left(B\right) = \{D \mid \operatorname{Matroid}.\operatorname{IsBase}\left(M, D\right), \lvert D \setminus B \rvert \le t\},\qquad\left(H_{t}\right)\left(B\right) = \max_{{D \in \left(N_{t}\right)\left(B\right)}} \operatorname{W}\left(D\right)
$$

These extrema are constructed, not supplied as hypotheses. Every base lies in the finite native ground M.E, so N_t(B) is a finite family of subsets of that ground (Set.Finite.finite_subsets and subset). It is nonempty since it contains B. The pinned Set.exists_max_image applied to W therefore supplies a base A in N_t(B) whose weight is H_t(B), dominating every member. This works for negative weights and does not use a supremum convention for an empty family. At radius zero, D minus B has cardinality zero, hence D is contained in B; the antichain property Matroid.IsBase.eq_of_subset_isBase gives D=B. Thus H_0(B)=W(B).

For every natural k and path B0,...,Bk of bases with |B(i+1) minus Bi| <= 1 for every 0 <= i < k, define err_i = H_1(Bi) - W(B(i+1)). The full known-source conclusion has both parts: each err_i is nonnegative, and every base C with |C minus B0| <= k satisfies the following bound:

$$
(\forall (i: \operatorname{Fin}\left(k\right)), (0 \le err_{i})) \land (\forall (C: \operatorname{Set}\left(E\right)), (((\operatorname{Matroid}.\operatorname{IsBase}\left(M, C\right)) \land (\lvert C \setminus B_{0} \rvert \le k)) \Rightarrow (\operatorname{W}\left(C\right) \le \operatorname{W}\left(B_{k}\right) + \sum_{{0 \leq i < k}} err_{i})))
$$

Nonnegativity follows immediately because B(i+1) belongs to N_1(Bi). To derive the comparator bound, first fix adjacent B0,B1 and any natural r. Lemma 4.1, with the paper's positive integer k replaced by r+1, is the joint neighborhood comparison:

$$
\left(H_{r + 1}\right)\left(B_{0}\right) + \operatorname{W}\left(B_{1}\right) \le \left(H_{r}\right)\left(B_{1}\right) + \left(H_{1}\right)\left(B_{0}\right)
$$

Choose A maximizing W in N_(r+1)(B0). The unspecified B in the printed initial argmax of Lemma 4.1 must be B0, as equation (21) requires. It suffices to construct one pair of bases D,F satisfying all three conditions together:

$$
\lvert D \setminus B_{1} \rvert \le r,\qquad\lvert F \setminus B_{0} \rvert \le 1,\qquad\operatorname{W}\left(A\right) + \operatorname{W}\left(B_{1}\right) \le \operatorname{W}\left(D\right) + \operatorname{W}\left(F\right)
$$

Indeed their weights are bounded above by H_r(B1) and H_1(B0), respectively, while W(A)=H_(r+1)(B0). The radius and weight inequalities must hold for this same pair; separate existential choices cannot be combined. In the notation below P-a+b means (P minus {a}) union {b}. For U contained in A minus B1 and V contained in B1 minus A, the simultaneous pair D=(A minus U) union V, F=(B1 minus V) union U preserves total weight W(D)+W(F)=W(A)+W(B1). Moreover |D minus B1|+|U|=|A minus B1|. These are finite indicator-sum and disjoint-difference identities, using the very same U,V.

If A already belongs to N_r(B1), take D=A,F=B1. If A=B0, take D=B1,F=B0; both required radii are zero and the weights merely commute. If B0=B1 and A differs from B0, choose a in A minus B1; nonemptiness follows from base antichainness. Symmetric singleton exchange gives b in B1 minus A with D=A-a+b and F=B1-b+a both bases. Their radii are |A minus B0|-1 <= r and 1, and their total weight is unchanged. The symmetric singleton fact is itself an instance of the existing prescribed-exchange theorem with X={a},Y=empty: the rank bound forces |U|=|V|=1.

Otherwise B0 and B1 are distinct. Equal base cardinalities and adjacency give B0 minus B1={x} and B1 minus B0={y}, so B1=B0-x+y and x differs from y. For any A, |A minus B1| plus the indicator of y in A equals |A minus B0| plus the indicator of x in A. This identity accounts for the radius change in each of the following membership cases.

If y belongs to A and x does not, |A minus B1|=|A minus B0|-1 <= r, so D=A,F=B1 works. If both x and y belong to A, symmetric exchange of x in A minus B1 supplies b in B1 minus A and bases D=A-x+b,F=B1-b+x. Here |D minus B1|=|A minus B0|-1 <= r and F minus B0={y}, so its radius is one. If neither x nor y belongs to A, symmetric exchange of y in B1 minus A supplies a in A minus B1 and bases D=A-a+y,F=B1-y+a. Since x is absent from A, a is outside B0; thus F minus B0={a}, and |D minus B1|=|A minus B0|-1 <= r. Both cases preserve total weight.

The remaining case has x in A and y outside A. Before choosing any minimum, use the already separated case A=B0: if A minus B0 were empty, A would be contained in B0 and base antichainness would force A=B0, a contradiction. Thus A minus B0 is nonempty. Apply the existing simultaneous theorem to the bases A,B1 with X={x},Y={y}. It supplies U contained in A minus B1 and V contained in B1 minus A, containing x,y respectively, with equal positive size at most rank({x,y}) <= 2, and both exchanged sets are bases. Here |A minus B1|=|A minus B0|+1.

For size two, write U={x,a},V={y,b} with distinct elements in each pair. Take D=(A minus U) union V and F=(B1 minus V) union U=B0-b+a. Then |D minus B1|=|A minus B1|-2=|A minus B0|-1 <= r and F minus B0={a}, while total weight is preserved. These are precisely the simultaneous bases from the supplier, so no compatibility step is missing.

For size one, U={x},V={y}, so A'=A-x+y is a base, but its radius need not yet be r. The pinned Set.exists_min_image on the finite nonempty A minus B0 chooses amin of minimum w-weight. Since (A' minus B1)=A minus B0, amin belongs to A' minus B1. Ordinary exchange (Matroid.IsBase.exchange) between A' and B1 supplies b in B1 minus A' with D=A'-amin+b a base. Here b is neither y nor x and is outside A, hence b belongs to B0 minus A. A second ordinary exchange, now between B0 and A removing b, supplies a in A minus B0 with F=B0-b+a a base. These two ordinary exchanges need not be symmetric; only the stated base conclusions are used.

The repaired D is A minus {x,amin} union {y,b}. Because x and amin are distinct elements of A minus B1 and y,b lie in B1, its radius is |A minus B1|-2=|A minus B0|-1 <= r. Also F minus B0={a}. Finite single-insertion/removal weight identities, with the stated membership conditions, give:

$$
\operatorname{W}\left(D\right) + \operatorname{W}\left(F\right) = \operatorname{W}\left(A\right) + \operatorname{W}\left(B_{1}\right) - \operatorname{w}\left(a_{min}\right) + \operatorname{w}\left(a\right) \geq \operatorname{W}\left(A\right) + \operatorname{W}\left(B_{1}\right)
$$

The final inequality is exactly w(amin) <= w(a), since a belongs to A minus B0. It closes the same-pair weight bound even for signed weights. This exhausts the x/y cases and proves the displayed joint comparison as an application of the existing exchange and extremum facts.

Rearrange the comparison at step i with r=k-i-1: H_(k-i)(Bi) <= H_(k-i-1)(B(i+1))+err_i. Iterating over the finite path gives, for k >= 1, the telescope:

$$
\left(H_{k}\right)\left(B_{0}\right) \leq \left(H_{k-1}\right)\left(B_{1}\right) + err_{0} \leq ... \leq \left(H_{0}\right)\left(B_{k}\right) + \sum_{{0 \leq i < k}} err_{i} = \operatorname{W}\left(B_{k}\right) + \sum_{{0 \leq i < k}} err_{i}
$$

Every radius-k comparator C has W(C) <= H_k(B0), yielding the announced bound. For k=0 the sum is empty, there are no error assertions, and base antichainness forces every radius-zero comparator to equal B0. Repeated bases are allowed; the coincident-base case above supplies their comparison. Proper or empty native grounds, empty carriers, rank zero, loops, coloops, intersecting bases and nonrepresentable matroids are all included. No strict improvement, optimal initial base, distinct-step or representation assumption is used. This is the known mathematical result of Theorem 1.7, with natural-radius indexing avoiding truncated subtraction; the exposition makes no new scope or literature-novelty claim and no algorithm, oracle-query, running-time or physical-realization claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PrescribedExchange.exists_prescribed_exchange`
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual](../Graph/LayeredCirculation/SupplierDual.md)
- Dependency: [D5/S3/Combinatorics/Matroids/FiniteIntersectionPolytope](FiniteIntersectionPolytope.md)
- Dependency: [D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation](NativeWeightedBaseRankSaturation.md)
