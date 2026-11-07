# Three Specified Circular Deletions

## Abstract

Three preselected distinct deletions reconstruct a nodup oriented circle on a fixed support of at least four labels; every prescribed pair fails.

Cycle identifies rotations and retains orientation. Fix a finite support A with at least four labels. The observations are actual CircularDeletionTransport.delete outputs, indexed by their known deleted labels. The labels a,b,c are chosen before observing either state. No reversal quotient, repeated labels, unlabeled deck or adaptive choice is included.

**Theorem 1.1 (Any Three Specified Labels Suffice).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; \forall a \in T,\; \forall b \in T,\; \forall c \in T,\; \forall C \in \mathrm{Cycle}\left(T\right),\; \forall D \in \mathrm{Cycle}\left(T\right),\; ((4 \le \mathrm{card}\left(A\right)) \land ((a \in A) \land ((b \in A) \land ((c \in A) \land (((\neg (a = b)) \land ((\neg (a = c)) \land (\neg (b = c)))) \land (((\mathrm{Nodup}\left(C\right)) \land (\mathrm{support}\left(C\right) = A)) \land (((\mathrm{Nodup}\left(D\right)) \land (\mathrm{support}\left(D\right) = A)) \land ((\mathrm{delete}\left(a, C\right) = \mathrm{delete}\left(a, D\right)) \land ((\mathrm{delete}\left(b, C\right) = \mathrm{delete}\left(b, D\right)) \land (\mathrm{delete}\left(c, C\right) = \mathrm{delete}\left(c, D\right))))))))))) \Rightarrow (C = D)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/ThreeSpecifiedDeletions.reconstruct_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose r in A outside {a,b,c}. Reuse DeletionReadoutReconstruction.rooted to represent both circles as r followed by a list. Since r survives each observation, CyclicInsertionGap.anchored_coe_injective turns equality of circular residuals into equality of the corresponding filtered tail lists. Three erasures distinguish arbitrary linear lists: induct on the first list, choose an erased label different from both current heads, identify the heads, then cancel any surviving common head in each of the three equalities and apply induction. This induction covers every finite length, including the empty tail, without enumeration. The private list lemma is consumed in this theorem. The original full-deck reconstruct theorem has a stronger observation hypothesis; its statement and proof remain the existing result.

**Theorem 1.2 (Every Specified Pair Has a Collision).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; \forall a \in T,\; \forall b \in T,\; ((4 \le \mathrm{card}\left(A\right)) \land ((a \in A) \land ((b \in A) \land (\neg (a = b))))) \Rightarrow (\exists C \in \mathrm{Cycle}\left(T\right),\; \exists D \in \mathrm{Cycle}\left(T\right),\; ((\mathrm{Nodup}\left(C\right)) \land (\mathrm{support}\left(C\right) = A)) \land (((\mathrm{Nodup}\left(D\right)) \land (\mathrm{support}\left(D\right) = A)) \land ((\neg (C = D)) \land ((\mathrm{delete}\left(a, C\right) = \mathrm{delete}\left(a, D\right)) \land (\mathrm{delete}\left(b, C\right) = \mathrm{delete}\left(b, D\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/ThreeSpecifiedDeletions.two_deletions_insufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any distinct a,b in A choose r outside {a,b}, and enumerate A minus {r,a,b} as a nodup list L. The actual circles r,a,b,L and r,b,a,L have exactly support A. Anchored uniqueness distinguishes them, while deletion of a gives r,b,L in both and deletion of b gives r,a,L in both. This direct pair-swap construction proves the observation-count boundary on an arbitrary common support. The existing three-label-support obstruction in DeletionReadoutReconstruction.deletion_joint_kernel_iff is independent background; this pair-collision proof does not use it.

The minimum-observation application uses the existing MinimumCompleteSetCover theorem without introducing a new budget framework. Its state type X is SupportedCircle A, its observer index type is the subtype A, its output family V(i) is Cycle T for each i in A, and q(i) is exactly deletionReadout A i. A selected nonadaptive budget J is a Finset A; jointReadout restricts q to the subtype of labels belonging to J. For every fixed support A of cardinality at least four, this selected joint readout is injective if and only if 3 <= J.card. For sufficiency select three members of J and apply reconstruct_three. If J has at most two members, enlarge it within A to a pair of distinct labels; two_deletions_insufficient supplies distinct supported circles agreeing on that pair and hence on J. This includes the empty and singleton budgets. The existing counterexample_certifies_incomplete_budget applies to that actual pair.

The existing finite_budget_injective_iff_cover identifies these complete deletion families with covers of all distinct ordered pairs of SupportedCircle A. Under the natural unit cost c(i)=1, budgetCost J c equals J.card. The existing minimum_complete_budget_iff_minimum_cover then says that IsMinimumCompleteBudget J (deletionReadout A) c holds exactly when J.card=3: every complete competitor has at least three members, and A contains a complete triple. All triples are therefore minimum, and every larger selected family is complete but has larger unit cost. These are exact applications of existing results, so their binding-only checks remain transient rather than new named D5 declarations. The cost counts exact deletion readouts of the same fixed object. A readout contains a whole residual circle of length |A|-1; the result does not bound the number of encoded bits, the cost of accessing or copying the object, running time, adaptive strategies, or recovery from noise.

On X = SupportedCircle(A), the triple map J(C) = (delete(a,C),delete(b,C),delete(c,C)) is injective. Direct application of Mathlib Finsupp.mapDomain_injective makes its pushforward injective on finitely supported signed masses and hence on finite probability laws. This concerns the joint pushforward from one sample. It does not identify the law from a family of individual marginal pushforwards, nor give a noise stability or sample complexity bound.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/ThreeSpecifiedDeletions.reconstruct_three`
- Truth anchor: `D5/S3/Combinatorics/CircularWords/ThreeSpecifiedDeletions.two_deletions_insufficient`
- Dependency: [D5/S3/Combinatorics/CircularWords/DeletionReadoutReconstruction](DeletionReadoutReconstruction.md)
