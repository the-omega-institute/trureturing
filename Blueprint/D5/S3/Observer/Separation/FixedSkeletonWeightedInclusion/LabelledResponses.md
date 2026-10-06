# Labelled Responses and Completion Geometry

## Abstract

The same labelled task admits a common suffix replay, same-law coordinate entropy and completion sorting.

Let I index pairs with distinct first and second coordinate labels. For each i, take nonempty alphabets X_i and Y_i, an output type Z_i, and a total map f_i:X_i times Y_i -> Z_i. Inputs range over the full independent product. An arbitrary total G on the product of Z_i defines the same task at both cuts. The index set and output types need not be finite for this replay equality.

A cut B is described by first-endpoint indices B_1 and second-endpoint indices B_2; a cut P has indices P_1 and P_2. Assume B_2 is contained in B_1, P_2 is contained in P_1, and P_2 is contained in B_2. A chosen subset A of I marks designated pairs. For ordinary indices outside A, every first endpoint read by B is also read by P. Each ordinary map has one surjective row and one surjective column, separately; no condition is imposed on its other slices. These conditions permit nonnested cuts.

Put E=A intersect (P_1 minus B_1). Every pair in E is untouched by B and opened only at its first endpoint by P. Group B prefixes only by designated endpoint values read in B and absent from P: first labels in A intersect (B_1 minus P_1), and second labels in A intersect (B_2 minus P_2). Write C_c for the group with these values equal to c. Values in B intersect P remain free within the group.

For x in the product of X_i over E, let S_x be the product of the row images f_i(x_i,Y_i). For z in S_x and an assignment d to all endpoints outside B and outside pairs E, H_z^b(d) applies G to z on E and to the actual pair outputs obtained by joining b and d elsewhere. Every H coordinate has exactly this same labelled residual domain. A P response uses the complete independent product of endpoints outside P as its suffix domain.

**Theorem 1.1 (One suffix for every prefix in a designated group).**

$$\exists q, \forall c,x,z,d, z\in S_{x}\implies \exists s, \forall b\in \mathcal{C}_{c}, R_{P}(q(x, b), s)=H_{z}^{b}(d).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses.nonnested_common_suffix_replay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a map q taking x and any B prefix b to an actual P prefix. For every c,x,z,d with z in S_x, one P suffix s works for every b in C_c: the P response at q(x,b), evaluated at s, equals H_z^b(d). The choice of s may depend on c,x,z,d, but is independent of the varying prefix b.

Choose a surjective ordinary row, a surjective ordinary column, and sections of these slices. On designated endpoints, q copies B values shared with P and inserts x at E. A designated B value absent from P is supplied by c in the suffix; a designated value absent from B is supplied by d. For each pair in E, choose its second endpoint to realize z in the selected row.

An ordinary pair completed in B and P copies both endpoints. If completed in B but its second endpoint lies outside P, q encodes its actual output using the column section and the suffix uses the fixed column endpoint. For a half-read ordinary B pair, q copies its first endpoint and the suffix copies its second endpoint from d. For an ordinary pair untouched by B but opened by P, q uses the fixed row endpoint and the suffix uses the row section to preserve its output in d. If untouched by both cuts, both endpoints come from d. Comparing every pair output proves the equality before applying the same G. Empty E, empty groups of designated labels, singleton alphabets and constant G are included.

**Theorem 1.2 (A finite fractional cover for a submodular function).**

$$\forall H,U,S,w, SubmodularCoverAssumptions(H, U, S, w)\implies L(H(U), sum(r, w_{r}H(S_{r}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses.fractional_submodular_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a type with decidable equality, R a finite row type, U a finite subset of A, and S_r subsets of U. H maps finite subsets of A to real numbers, H(empty)=0, H is monotone under inclusion, and H(s union t)+H(s intersection t)<=H(s)+H(t). The real weights w_r are nonnegative, and every a in U has sum of incident w_r at least 1. SubmodularCoverAssumptions denotes exactly these premises, and L(a,b) denotes a<=b. Then H(U)<=sum_r w_r H(S_r). Empty U, empty selected sets, repeated row labels and zero weights are allowed. The proof inducts on U using the contracted function H(insert a,t)-H({a}) and the actual weighted incidence of a.

**Theorem 1.3 (Fractional coordinate entropy on one actual law).**

$$\forall p,u,S,w, LawAndCover(p, S, w)\implies L(H_{p}(A), sum(r, w_{r}H_{p}(S_{r}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses.weighted_coordinate_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

X,A,R are arbitrary finite sample, attribute and row types. V_a are finite, possibly different value types. p:X->real is nonnegative and sums to 1. Each u_a:X->V_a is an actual readout. For S subset A, tuple_S(x)=(u_a(x)) for a in S, and H_p(S) is Shannon entropy in nats of pushforward tuple_S p. Every law is a literal pushforward of this same p. L means <=. LawAndCover denotes p>=0, sum p=1 and the following cover premises. The real row weights w_r are nonnegative and their sum over rows containing each attribute is at least 1. No independence or positive marginal premise is used. Empty selected subsets have singleton tuple carrier and entropy 0; repeated rows and zero weights remain included. This statement alone does not prove the original fixed-skeleton global bounds, literal minimum or Boolean sharpness.

## References

- Truth anchor: `D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses.fractional_submodular_cover`
- Truth anchor: `D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses.nonnested_common_suffix_replay`
- Truth anchor: `D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses.weighted_coordinate_entropy`
- Dependency: [D5/S3/Entropy/EntropyEquality](../../../Entropy/EntropyEquality.md)
- Dependency: [D5/S3/Entropy/Forgetting/CompletionEntropyMinimality](../../../Entropy/Forgetting/CompletionEntropyMinimality.md)
- Dependency: [D5/S3/Entropy/Forgetting/DeterministicEntropyEquality](../../../Entropy/Forgetting/DeterministicEntropyEquality.md)
- Dependency: [D5/S3/Entropy/Forgetting/PushforwardComposition](../../../Entropy/Forgetting/PushforwardComposition.md)
- Dependency: [D5/S3/Entropy/Submodularity/StrongSubadditivity](../../../Entropy/Submodularity/StrongSubadditivity.md)
