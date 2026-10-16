# Countably compact injective closing-off

## Abstract

Fresh accumulation-point supply constructs a countably compact injective extension of every continuum-sized admissible seed.

All object types X, B and I are in Type, and c denotes the continuum. The map q is arbitrary. FreshClusterSupply(Good,q) means the following: for every embedding e from the natural numbers into X with range(e) contained in Good and q composed with e injective, and every F contained in B of cardinal at most c, there is x in Good with AccPt x (principal(range(e))) and q(x) outside F. AccPt and IsCountablyCompact have their ambient Mathlib meanings.

**Theorem 1.1 (Simultaneous representatives with distinct values).**

$$\forall X: Type, \forall B: Type, \forall q: X \to B, \forall I: Type, \forall A: I \to \operatorname{Set}\left(X\right), \forall H: \operatorname{Set}\left(X\right), {\operatorname{Card}\left(I\right) \le c \land \operatorname{Card}\left(H\right) \le c \land \forall i: I, \forall F: \operatorname{Set}\left(B\right), {\operatorname{Card}\left(F\right) \le c} \Rightarrow \exists x: X, x \in \operatorname{A}\left(i\right) \land \neg{\operatorname{q}\left(x\right) \in F}} \Rightarrow \exists f: I \to X, {\forall i: I, \operatorname{f}\left(i\right) \in \operatorname{A}\left(i\right)} \land \operatorname{Injective}\left(\operatorname{compose}\left(q, f\right)\right) \land \forall i: I, \neg{\operatorname{q}\left(\operatorname{f}\left(i\right)\right) \in \operatorname{image}\left(q, H\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CountablyCompact/InjectiveSelectorClosure.exists_fresh_choice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any family of at most c tasks, each admitting a witness outside every at most c forbidden set of q-values, well-founded recursion along WellOrderingRel constructs one representative for each task. At task i, forbid q(H) and the image of all earlier representatives. Each prefix has cardinal at most that of the entire task type; its image together with q(H) has cardinal at most c. The recursion equation proves membership, pairwise distinct q-values and avoidance of q(H). No regularity of c, injectivity on H, or topology is required for this helper.

**Theorem 1.2 (Actual countably compact extension).**

$$\forall X: Type, \forall B: Type, \forall q: X \to B, \operatorname{TopologicalSpace}\left(X\right) , \operatorname{TOneSpace}\left(X\right) , \forall Good: \operatorname{Set}\left(X\right), \forall Szero: \operatorname{Set}\left(X\right), {\operatorname{FreshClusterSupply}\left(Good, q\right) \land Szero \subseteq Good \land \operatorname{Card}\left(Szero\right) \le c \land \operatorname{InjOn}\left(q, Szero\right)} \Rightarrow \exists S: \operatorname{Set}\left(X\right), Szero \subseteq S \land S \subseteq Good \land \operatorname{Card}\left(S\right) \le c \land \operatorname{InjOn}\left(q, S\right) \land \operatorname{IsCountablyCompact}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CountablyCompact/InjectiveSelectorClosure.exists_countablyCompact_injOn_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

X is an arbitrary T1 space. Starting with any Szero contained in Good, of cardinal at most c, and on which q is injective, the conclusion constructs S containing Szero, contained in Good, of cardinal at most c, with q injective on S and S countably compact. Empty and finite seeds are included. No continuity of q, first countability, sequential compactness, CH, MA, or regularity of the continuum is assumed.

For one step from S, the task type is all embeddings from the natural numbers into S. Its cardinal is bounded by Card(S) to the power aleph0, hence by c. Fresh simultaneous choice adds an ambient accumulation point for each embedding, avoiding both q(S) and the values of earlier new points. The resulting extension is small, good and injective. The tasks at this step refer to S, so later steps process newly added points.

Use omega1.ToType as the index type. The actual well-founded recursion defines stage(i) as Szero union all one-step extensions of stage(j) for j less than i. The recursion equation proves that zero is Szero, a successor is the one-step extension of its predecessor, and a nonzero limit is the union of its earlier stages. Induction using these equations proves containment in Good, the cardinal bound and injectivity; the stages form an increasing chain. The final union is small because aleph1 is at most c. For an infinite subset, select an embedding of the natural numbers into it. Ordinal.iSup_lt_omega_one bounds all appearance stages below omega1. The next stage supplies an ambient AccPt of the range, which remains an AccPt of the original larger subset. The native infinite-subset characterization proves IsCountablyCompact.

This is a classical transfinite closing-off argument, independently implemented using Mathlib. Feldman and Wilce, A Note on Compactness and Clique Size, arXiv:2608.13320v1, Question 1 on page 5 and the sufficient construction on page 10, provide the research target. The present theorem supplies the generic closure step; it does not assert that the paper already constructs its missing set Y. Application to that question still requires free-ultrafilter cardinal supply, fresh good accumulation points, a section-dense seed, and the graph argument. The closure method is not claimed novel.

## References

- Truth anchor: `D5/S3/Topology/CountablyCompact/InjectiveSelectorClosure.exists_countablyCompact_injOn_extension`
- Truth anchor: `D5/S3/Topology/CountablyCompact/InjectiveSelectorClosure.exists_fresh_choice`
