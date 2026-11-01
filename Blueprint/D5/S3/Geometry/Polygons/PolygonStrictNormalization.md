# Two original families with independent conditioned totals

## Abstract

Strict normalized bounds for full conditioned polygon families

**Theorem 1.1 (Two nonempty cross-intersecting families have normalized sum below one).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], ((14 \leq n) \implies (\forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Disjoint}\left(P, Q\right) \implies ((\forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in (P \cup Q)) \implies (\forall j \in \operatorname{ZMod}\left(n\right),\; ((j \in (P \cup Q)) \implies ((i \neq j) \implies \neg\operatorname{Cross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(j\right)\right)))))) \implies ((((\operatorname{card}\left(P\right) = 2) \land (\operatorname{card}\left(Q\right) = 2)) \lor (((\operatorname{card}\left(P\right) = 3) \land (\operatorname{card}\left(Q\right) = 3)) \lor (((\operatorname{card}\left(P\right) = 2) \land (\operatorname{card}\left(Q\right) = 4)) \lor ((\operatorname{card}\left(P\right) = 4) \land (\operatorname{card}\left(Q\right) = 2))))) \implies (\forall A \in \operatorname{Finset}\left(\operatorname{WholeFiber}\left(P, Q\right)\right),\; \forall B \in \operatorname{Finset}\left(\operatorname{WholeFiber}\left(Q, P\right)\right),\; ((\forall T \in \operatorname{WholeFiber}\left(P, Q\right),\; ((T \in A) \implies (\forall U \in \operatorname{WholeFiber}\left(Q, P\right),\; ((U \in B) \implies \neg\operatorname{Disjoint}\left(\operatorname{EarCenters}\left(\operatorname{val}\left(T\right)\right), \operatorname{EarCenters}\left(\operatorname{val}\left(U\right)\right)\right))))) \implies (\operatorname{Nonempty}\left(A\right) \implies (\operatorname{Nonempty}\left(B\right) \implies ((\frac{\operatorname{Real}\left(\operatorname{card}\left(A\right)\right)}{\operatorname{Real}\left(\operatorname{Natcard}\left(\operatorname{WholeFiber}\left(P, Q\right)\right)\right)} + \frac{\operatorname{Real}\left(\operatorname{card}\left(B\right)\right)}{\operatorname{Real}\left(\operatorname{Natcard}\left(\operatorname{WholeFiber}\left(Q, P\right)\right)\right)}) < 1))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonStrictNormalization.original_normalized_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an arbitrary natural n at least 14 and derive NeZero(n) from this inequality. The vertices are ZMod(n), ear(i) is the chord with endpoints i-1 and i+1, and EarCenters(T) is the complete set of centres of ears present in T. The arbitrary finite sets P,Q are disjoint, their union K has pairwise noncrossing ears, and their ordered cardinalities (p,q) are (2,2), (3,3), (2,4), or (4,2). There is no restriction on their cyclic placement.

WholeFiber(P,Q) is definitionally ConditionFiber(P,Q,empty,empty): every maximal noncrossing finite set T of actual internal diagonals with P contained in EarCenters(T) and Q disjoint from EarCenters(T). The empty observation imposes no further condition. Thus WholeFiber(Q,P) is a separate full conditioned type on the same polygon. A and B are arbitrary finite subfamilies of these respective types, and every T in A and U in B has a common ear in their full EarCenters sets. In the formula Natcard denotes Nat.card, card denotes Finset.card, and every division and addition in the conclusion takes place in Real.

For H contained in E_K, let w(R) be the real cast of Nat.card(ConditionFiber(P,Q,H,R)). When the ears centred in H are pairwise noncrossing, the actual conditioned trace flip injects the fibre with trace insert(h,R) into the fibre with trace R. Finite insertion induction gives w(S) at most w(R) whenever R is contained in S contained in H. This argument retains zero fibres and uses no positivity assumption on individual traces.

For every h in H, source_conditioned_witnesses supplies an actual member of the empty-trace fibre containing two distinct diagonals crossing ear(h). Every image of the singleton flip has at most one such chord, since all retained chords coexist with ear(h) in its input. That supplied fan lies outside the image, so w({h}) is strictly below w(empty). Integrality and antitonicity give w(R)+1 at most w(empty) for every nonempty R contained in H.

The complete fibres partition WholeFiber(P,Q) by T mapped to EarCenters(T) intersect H. Equiv.sigmaSubtypeFiberEquiv supplies the finite-fibre partition, with only the ConditionFiber subtype identification performed locally. Summing over every R contained in H gives exactly Nat.card(WholeFiber(P,Q)); the empty trace and every actual completion remain in this total.

On the finite distributive lattice of subsets of H, the proof applies the pinned Mathlib fkg inequality to the monotone functions w(bottom)-w and the indicator of a relatively upper family C. Subtracting one unit at bottom preserves antitonicity by the integer gap. Since C is nonempty and omits bottom, this yields mass(w,C)/sum(w) strictly below card(C)/card(powerset(H)). The positive whole-fibre total comes from source_conditioned_witnesses. The local signed-shift and bottom-subtraction helpers are consumed applications of fkg.

exists_original_terminal_compression supplies the same H for both original families and upper families C,D contained in powerset(H), with the original cardinalities bounded by the two respective weighted masses. Both upper families are nonempty and cross-intersecting. The complement map R mapped to H minus R injects D into a family disjoint from C, so card(C)+card(D) is at most card(powerset(H)). Apply the strict weighted comparison independently to P given Q and Q given P, add the bounds, and obtain the displayed strict inequality.

Application with the explicit Catalan denominators.

For the full B-37.2 application, retain all the hypotheses above but allow A or B to be empty. Define the integer function Npq as follows; Catalan(k) is the natural Catalan number, choose(q,j) is the binomial coefficient, and n-p-j-2 uses natural subtraction.

$$
\forall n \in Nat,\; \forall p \in Nat,\; \forall q \in Nat,\; (\operatorname{Npq}\left(n, p, q\right) = \sum _{j\in \operatorname{range}\left((q + 1)\right)} ((((-1)^{j} \cdot \operatorname{Int}\left(\operatorname{choose}\left(q, j\right)\right)) \cdot \operatorname{Int}\left(\operatorname{Catalan}\left((((n - p) - j) - 2)\right)\right))))
$$

The pairwise noncrossing hypothesis on K is exactly PolygonEarContraction.Compatible(K). Apply PolygonConditionalCounts.conditional_card first to P,Q and then separately to Q,P, using disjointness in the corresponding orientation. WholeFiber is the complete fibre with empty observation, so these applications give the two integer identities below. They do not identify the two denominators.

$$
((\operatorname{Int}\left(\operatorname{Natcard}\left(\operatorname{WholeFiber}\left(P, Q\right)\right)\right) = \operatorname{Npq}\left(n, p, q\right)) \land (\operatorname{Int}\left(\operatorname{Natcard}\left(\operatorname{WholeFiber}\left(Q, P\right)\right)\right) = \operatorname{Npq}\left(n, q, p\right)))
$$

Apply PolygonConditionedFan.source_conditioned_witnesses in each orientation, swapping the ordered cardinality case and rewriting union_comm for the second. Its nonempty whole-fibre witness and positive Nat.card give Npq(n,p,q)>0 and Npq(n,q,p)>0 in Int. Casting each integer identity to Real gives separately Nat.card(WholeFiber(P,Q))=Npq(n,p,q) and Nat.card(WholeFiber(Q,P))=Npq(n,q,p), with both right sides positive and nonzero in Real. These are casts of two actual counts, not assumptions or a symmetry assertion.

For every actual T in WholeFiber(P,Q) and U in WholeFiber(Q,P), PolygonSimultaneousCompression.common_ears_eq_trace_inter supplies the full common-ear identity below. E_K is the set of centres outside K whose ears are compatible with every ear in K. The identity transports the full-ear cross-intersection premise to the common observation carrier without requiring intersection inside a selected six-ear set.

$$
(\operatorname{inter}\left(\operatorname{EarCenters}\left(\operatorname{val}\left(T\right)\right), \operatorname{EarCenters}\left(\operatorname{val}\left(U\right)\right)\right) = \operatorname{inter}\left(\operatorname{inter}\left(\operatorname{EarCenters}\left(\operatorname{val}\left(T\right)\right), \operatorname{EK}\left((P \cup Q)\right)\right), \operatorname{inter}\left(\operatorname{EarCenters}\left(\operatorname{val}\left(U\right)\right), \operatorname{EK}\left((P \cup Q)\right)\right)\right))
$$

Write S for the following expression in Real, with the integer Npq values cast individually.

$$
(S = (\frac{\operatorname{Real}\left(\operatorname{card}\left(A\right)\right)}{\operatorname{Real}\left(\operatorname{Npq}\left(n, p, q\right)\right)} + \frac{\operatorname{Real}\left(\operatorname{card}\left(B\right)\right)}{\operatorname{Real}\left(\operatorname{Npq}\left(n, q, p\right)\right)}))
$$

If A and B are both nonempty, apply original_normalized_strict and rewrite its two whole-fibre denominators by their own cast count identities. This gives S<1. If A is empty, S=card(B)/Npq(n,q,p); Finset.card_le_univ bounds card(B) by Fintype.card(WholeFiber(Q,P))=Nat.card(WholeFiber(Q,P)). Dividing by its positive real total gives S<=1. If B is empty, use the separate bound for A and Npq(n,p,q). If both are empty, S=0.

$$
(S \leq 1)
$$

Equality cannot occur with both families nonempty. With A empty, S=1 is equivalent, by positivity of Npq(n,q,p), to card(B)=Nat.card(WholeFiber(Q,P)); Fintype.card and Finset.eq_univ_of_card then give B=univ on its own whole fibre. Conversely B=univ has precisely that total, so S=1. With B empty the same reasoning uses Npq(n,p,q) and A=univ on WholeFiber(P,Q). Positive whole totals exclude the both-empty pair from equality. Thus the exact equality classification is:

$$
((S = 1) \iff (((A = \emptyset) \land (B = \operatorname{univ}\left(\operatorname{WholeFiber}\left(Q, P\right)\right))) \lor ((B = \emptyset) \land (A = \operatorname{univ}\left(\operatorname{WholeFiber}\left(P, Q\right)\right)))))
$$

This application includes all n at least 14, all four ordered size cases, arbitrary compatible placements, every actual completion, and separate counts in the two orientations. It is a consequence of the strict theorem, the original count and fan results, the common-ear identity, and finite-cardinality facts. No separate named upper-bound, equality, count, cast or final-application theorem is needed.

Six labelled complementary graphs.

Fix any n at least 14 and any labelled set D of polygon vertices. Let M indexed by Fin(3) be three pairwise disjoint matchings of ear centres, each of cardinality two, with M(0) union M(1) union M(2)=D. Assume the original ear chords centred in D are pairwise noncrossing. These hypotheses allow arbitrary compatible placements; there is no cyclic symmetry or position assumption. The labels form the dependent sum of the pairs (i,x) with i in Fin(3) and x in M(i). Its cardinality is 2+2+2=6. For each i, let j<k be the other two zero-based indices: (j,k)=(1,2),(0,2),(0,1) for i=0,1,2 respectively. This determines the indices uniquely and does not identify different polygon placements.

For the label (i,x), set P=M(j) union {x} and Q=M(k) union (M(i) minus {x}). Pairwise disjointness makes x absent from both M(j) and M(k), so card(P)=2+1=3 and card(Q)=2+(2-1)=3. The same hypotheses give Disjoint(P,Q), P union Q=D, card(D)=6, D minus P=Q and D minus Q=P. These are derived partition facts. For either orientation b, let S=P and S'=Q when b is false, and S=Q and S'=P when b is true. In particular S'=D minus S in both orientations.

Define Gamma_D(S) to be the subtype of all actual triangulations T with EarCenters(T) intersect D=S. A triangulation is its entire finite set of internal diagonals, with the maximal noncrossing predicate used by PolygonEarSlide.Carrier.IsTriangulation. No other ear or diagonal is restricted. Since S and S' partition D, the displayed trace equality is equivalent to S being contained in EarCenters(T) and S' being disjoint from EarCenters(T). Thus the identity on underlying chord sets is a bijection from Gamma_D(S) to PolygonSimultaneousCompression.WholeFiber(S,S'), and the analogous identity identifies Gamma_D(S') with WholeFiber(S',S). Both maps and inverses preserve every chord. The nonempty disjoint sets S,S' also imply that vertices on opposite sides have distinct chord sets: equality would force their D-traces S and S' to coincide.

Put X=Gamma_D(S) and Y=Gamma_D(S'). Join T in X to U in Y exactly when their chord sets differ and their complete EarCenters sets are disjoint. Under the two bijections this is exactly the full-ear disjointness relation on the respective WholeFiber types. It is not a relation merely on the D-traces. For every finite subset A of the entire X, define N_Y(A) to be all U in Y adjacent to some T in A. Mapping A and its neighborhood by the bijections gives exactly the corresponding WholeFiber subset and neighborhood; finite cardinalities, the empty subset and the full subset are preserved.

Apply PolygonConditionalCounts.conditional_card and PolygonConditionedFan.source_conditioned_witnesses separately in the two orientations, as above, now with ordered sizes (3,3). They give card(X)=card(Y)=Npq(n,3,3)>0, first as actual natural-cardinality identities in Int and then by positive casts in Real. The equal totals here follow from substituting the same ordered sizes into the two count identities. They impose no symmetry assertion for other size cases.

For any A contained in X, put B=Y minus N_Y(A). Every T in A and U in B has a common ear: otherwise their distinct chord sets and disjoint full ear sets would make them adjacent, contradicting U not in N_Y(A). Apply the preceding weak normalized bound to A,B and their equal positive totals. Since card(B)=card(Y)-card(N_Y(A)), it gives card(A)<=card(N_Y(A)). This is Hall's inequality for every finite subset of the complete left carrier, without a restriction to subsets of some separately selected admissible family.

If A is nonempty and proper and B is nonempty, original_normalized_strict makes that inequality strict. If B is empty, N_Y(A)=Y, and properness gives card(A)<card(X)=card(Y), again strictly. The empty neighborhood of the empty subset follows directly from its definition. Applying Hall's inequality to the full X gives card(Y)<=card(N_Y(X)); the reverse inequality follows from containment in Y, hence N_Y(X)=Y. Consequently equality in Hall's inequality holds exactly for A empty or A=X. Full saturation uses the weak normalized bound; it requires no triangulation whose complete ear set is exactly S.

$$
\forall A \in \operatorname{Finset}\left(X\right),\; ((\operatorname{card}\left(A\right) \leq \operatorname{card}\left(N_{Y}\left(A\right)\right)) \land ((((A \neq \emptyset) \land (A \neq X)) \implies (\operatorname{card}\left(A\right) < \operatorname{card}\left(N_{Y}\left(A\right)\right))) \land ((\operatorname{card}\left(A\right) = \operatorname{card}\left(N_{Y}\left(A\right)\right)) \iff ((A = \emptyset) \lor (A = X)))))
$$

All signed integer deficits card(A)-card(N_Y(A)) are therefore at most zero, and the empty subset attains zero. Hence zero is the greatest element of the set of these deficits. Finiteness makes this the actual maximum over all subsets of X. Every count, adjacency identification, Hall inequality, strict proper expansion, empty/full neighborhood identity, equality classification and maximum-deficit assertion holds for each of the six dependent labels and independently in both orientations.

At the minimum allowed n=14, the matchings {0,2}, {4,6} and {8,10} in ZMod(14) satisfy the pair cardinalities, disjointness and actual ear compatibility. The same conclusion applies to all six of their labels in both orientations. The symbolic argument above covers arbitrary compatible labelled D for every n at least 14; this inhabited boundary example adds no position restriction. This graph application composes the canonical strict-normalization, conditioned-count, conditioned-fan and common-ear results with finite-set and bijection identities. It asserts neither the B-33.6 partition nor the complete-double-ear branch maximum L, the twelve-family classification or the global residual Kres.

Complementary path loss in one actual family.

Use six distinct labels f(i,b), with i in Fin(3) and b in Fin(2), on ZMod(n), for any n at least 14. The injective map f assigns f00,f01,f10,f11,f20,f21 to the abstract edges 12,34,13,24,14,23 respectively. Let D be its image and M_k={f(k,0),f(k,1)}. Then D has cardinality six and is the disjoint union of the three two-element matchings. Require pairwise noncrossing actual ears centred in D; shared chord endpoints are allowed. The abstract four-vertex edge labels specify incidence only and impose no order or symmetry on the polygon vertices.

The four complete stars are S_0={f00,f10,f20}, S_1={f00,f11,f21}, S_2={f01,f10,f21}, S_3={f01,f11,f20}. Fix any prescribed four witnesses W_a in one finite family F of actual triangulations, with full EarCenters(W_a)=S_a, for a in Fin(4). Require full-ear intersection only for distinct members T,U of this same F. For each k in Fin(3), require an actual U_k in F with EarCenters(U_k) intersect D=M_k. The active-core witnesses need not be chosen uniquely and their ears outside D are unrestricted. All statements below quantify over every such f,W,F, rather than selecting different families for different paths.

In finite-set notation define Gamma(D,R)={T : IsTriangulation(T) and EarCenters(T) intersect D=R}, where T ranges over all finite chord sets on the original polygon. This is the entire finite set of actual completions with that D-trace. Its subtype is the Gamma_D(R) used above. If P,Q partition D, the identity on underlying chord sets identifies its P subtype with WholeFiber(P,Q), and its Q subtype with WholeFiber(Q,P). The selections A=F intersect Gamma(D,P) and B=F intersect Gamma(D,Q) correspond respectively to all elements of those WholeFiber types whose underlying chord sets belong to F. These bijections preserve their cardinalities and all full-ear intersection statements; no completion or outside-D ear is discarded.

For any complementary three-element P,Q, conditional_card in the two orientations gives (card(Gamma(D,P)):Int)=Npq(n,3,3)=(card(Gamma(D,Q)):Int). Put w3(n)=toNat(Npq(n,3,3)). Thus card(Gamma(D,P))=Nat.card(WholeFiber(P,Q))=w3(n), and separately card(Gamma(D,Q))=Nat.card(WholeFiber(Q,P))=w3(n). The source_conditioned_witnesses positivity gives w3(n)>0, so its integer cast equals Npq(n,3,3) and its real cast is positive. Expanding the preceding inclusion-exclusion formula gives Npq(n,3,3)=Catalan(n-5)-3*Catalan(n-6)+3*Catalan(n-7)-Catalan(n-8), with each Catalan value cast to Int and natural subtraction in the indices. Equality of these two totals follows from their common ordered sizes (3,3).

First suppose A and B are both nonempty. Their distinct complementary D-traces make every cross-side pair different as actual chord sets. Hence the distinct-member full-ear intersection condition on F supplies exactly the cross-family hypothesis of original_normalized_strict after the identity transports above. Substitute the two positive whole-fibre totals to get card(A)/w3(n)+card(B)/w3(n)<1 in Real, hence card(A)+card(B)<w3(n). Integrality gives card(A)+card(B)<=w3(n)-1 in Nat and, after casting the counts separately, in Int. The pair inequality is a consequence of the actual family hypotheses, not an extra assumption.

The empty-side case uses an actual omitted completion. More generally, let R be a three-element subset of the compatible D and let M be an active two-element D-trace disjoint from R. Choose U in this same F with EarCenters(U) intersect D=M and h in M. PolygonCompressionTrace.independent_iff_noncrossing makes D cyclically independent, and earCenters_independent makes the full EarCenters(U) independent. Therefore h-1,h+1 lie outside both D and EarCenters(U), while h is outside R. Apply PolygonConditionedFan.fan_triangulation to the literal fan(R,h): it is an actual complete triangulation T, with R contained in EarCenters(T) contained in R union {h-1,h+1}. Consequently T belongs to Gamma(D,R). Any common ear with U would either lie in R intersect M, which is empty, or be h-1 or h+1, also excluded. Thus their full ear sets are disjoint. They are distinct since h belongs to EarCenters(U) and is absent from EarCenters(T). The distinct-member condition on F forces T not to belong to F. This construction uses no restriction on U's other outside-D ears; the literal fan construction remains supplied by PolygonConditionedFan.

In the generic complementary case suppose an active two-element trace M is disjoint from P and an active two-element trace N is disjoint from Q, both witnessed in F. Apply the omitted-completion argument to (R,M)=(P,M) and (R,M)=(Q,N). Each selected side is a proper subset of its own entire fibre, so card(A)<=w3(n)-1 and card(B)<=w3(n)-1 individually. If A is empty use the latter bound; if B is empty use the former. If both are empty the pair sum is zero and w3(n)>0 still gives the same bound. Together with the nonempty argument this proves card(A)+card(B)<=w3(n)-1 over the full domain, both in Nat and in Int. No selected-side nonemptiness or saturation premise is needed.

For the original path correspondence, fix k and let i<j be the other two matching indices: (i,j)=(1,2),(0,2),(0,1) when k=0,1,2. For each x in M_k put P_x=M_i union {x} and Q_x=M_j union (M_k minus {x}). Under the abstract edge labels these are complementary three-edge paths. Injectivity of f gives card(P_x)=card(Q_x)=3, Disjoint(P_x,Q_x), and P_x union Q_x=D. Moreover P_x is disjoint from M_j, and Q_x is disjoint from M_i. The original active witnesses U_j,U_i therefore supply the two generic omission inputs, in the required orientations, within the same F. The four prescribed W_a retain their full-star equalities in this original domain; the pair estimate itself uses only the actualness, distinct-member intersection and active-core hypotheses.

Write a_x=card(F intersect Gamma(D,P_x)), b_x=card(F intersect Gamma(D,Q_x)), and t_k=sum over x in M_k of (a_x+b_x). There are exactly two complementary path pairs in this sum, because M_k has exactly two elements. Each satisfies a_x+b_x+1<=w3(n), including either or both empty selected sides. Summing these two inequalities gives t_k+2<=2*w3(n). Define ell_k=2*w3(n)-t_k in Nat; the preceding inequality justifies this subtraction and gives ell_k>=2. Casting the individual a_x,b_x to Int and taking the same two-term sum gives the same t_k+2<=2*w3(n) and ell_k>=2 with integer subtraction. This holds for every k in Fin(3), so all three losses are at least two simultaneously for the original single family.

A complete instance exists already at n=14. Take D={0,2,4,6,8,10} and (f00,f01,f10,f11,f20,f21)=(0,8,2,6,10,4). Use the four literal fans with (forced set,root) equal to ({0,2,10},1), ({0,4,6},5), ({2,4,8},3), ({6,8,10},7), in star order. Their forced sets are independent and their roots lie outside them. Both root neighbours lie in the corresponding forced star, so fan_triangulation gives full EarCenters equality with S_0,S_1,S_2,S_3 respectively.

For the three active cores in that instance use the literal fans ({0,8,12},2), ({2,6,12},0), ({4,10,12},0). Their exact D-traces are M_0={0,8}, M_1={2,6}, M_2={4,10}, since the possible additional ears are confined respectively to {1,3}, {13,1}, {13,1}, all outside D. All three contain the actual outside-D ear 12. Let F be exactly these seven fans. The seven D-traces are distinct, so F has seven distinct actual members. Every pair of forced sets intersects, giving full-ear intersection within this same F. Thus the four complete stars and all three active cores coexist in the original domain. Here w3(14)=1727, so for every k the conclusions are t_k+2<=3454 and ell_k>=2 in Nat and Int. This instance establishes nonvacuity without enumerating all triangulations or asserting path-count sharpness.

This application reuses the frozen normalized strict, conditioned-count, fan and ear-independence results. It requires no A>W, saturation, parity, polygon symmetry or fixed protection carrier for outside ears. It establishes the complementary-pair inequalities and all three stated path losses only; it does not establish the full B-37.7 partition or deficit and equality chains, a global maximum, n24 or Kres.

For arbitrary P, the strict-normalization theorem does not assert an exact completion with EarCenters(T)=P, the n-p-3 degree or rank formula, or the stronger intermediate trace and rank formula chains. The strict argument uses the two-crossing fan and FKG comparison. It gives no equality between Npq(n,p,q) and Npq(n,q,p), and no general classification outside the four ordered cases. The polygon gap and its composition are repository derivations; the generic FKG, finite-cardinality and reindexing steps are applications of pinned Mathlib results.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonStrictNormalization.original_normalized_strict`
- Dependency: [D5/S3/Geometry/Polygons/PolygonConditionedFan](PolygonConditionedFan.md)
- Dependency: [D5/S3/Geometry/Polygons/PolygonSimultaneousCompression](PolygonSimultaneousCompression.md)
- Dependency: [D5/S3/Geometry/Polygons/PolygonTraceFlip](PolygonTraceFlip.md)
