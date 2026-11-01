# A Weighted Cross-Intersection Layer Gap

## Abstract

Nonnegative rank weights and cross-intersection force a gap between the coatom and singleton layers.

**Definition 1.1 (Rank-weighted mass).**

Lean statement: `D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap.weightedMass`

*Formalization.* `D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap.weightedMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite carrier alpha and a finite family C of its subsets, weightedMass(omega,C) is the sum of omega(card(A)) over all A in C. The function omega assigns one real weight to each natural rank; the definition itself imposes no sign or monotonicity condition.

**Theorem 1.2 (The coatom layer exceeds the singleton layer by at least two).**

Lean statement: `D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap.weighted_cross_intersecting_layer_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap.weighted_cross_intersecting_layer_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha be any finite type with decidable equality, and put d=card(alpha). Assume d is at least four. Let omega be an arbitrary function from natural ranks to real numbers such that every weight is nonnegative. Zero weights are allowed, and no relation between weights at different ranks is required. Let C and D be finite families of subsets of alpha. Both families are upward closed under inclusion, and every member of C has nonempty intersection with every member of D. Suppose each family's weighted mass is strictly greater than omega(d-1)+omega(d). Then card(C.slice(1))+2 is at most card(C.slice(d-1)). Here slice(r) keeps exactly the members of cardinality r. The nonnegative weights and strict mass bounds also imply that both families are nonempty.

For a finite set J in a larger ambient type, take alpha to be the subtype of elements of J. Its finite subsets are exactly subsets of J through the canonical inclusion. This identifies the statement for every finite J, with d=card(J), without choosing an ordering or restricting the original carrier to a particular labelled set.

If every member of a family contains a fixed coatom, its only possible members are that coatom and the full carrier. Nonnegativity bounds its mass by the sum of the coatom and top weights. Thus an upward family above this threshold has at least two coatoms: with at most one missing-point index, every member would contain the corresponding coatom.

Let t be the number of singletons in C. Cross-intersection forces every member of D to contain all t selected points. If t were at least d-1, every member of D would contain a fixed coatom, contradicting its strict mass bound. Hence t+2 is at most d. If t=0, the two-coatom bound proves the result. If t=1, upward closure includes at least d-1 coatoms, giving a gap of at least d-2, which is at least two. If t is at least two, every coatom contains a selected singleton, so all d coatoms belong to C and the result follows. The upward-closure hypothesis on D is retained in the statement, although this argument uses only its mass and cross-intersection.

This theorem concerns arbitrary weighted families of finite subsets. Applying it to polygon completions requires a separate encoding of those completions, a proof that the resulting families satisfy these hypotheses, and any required compression or identification of families. Those constructions are outside this theorem.

**Theorem 1.3 (A binomial threshold forces the variable gap on both sides).**

Lean statement: `D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap.weighted_cross_intersecting_layer_gap_of_binomial_threshold`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap.weighted_cross_intersecting_layer_gap_of_binomial_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha be any finite type with decidable equality, d=card(alpha), d>=3, and let k be any natural number with k<=d-3. For arbitrary real rank weights omega(r)>=0 define H(d,k)=sum(j=0,...,k) binom(k,j)*omega(d-j). Let C,D be upper families of subsets of alpha, cross-intersecting in the sense that every set on one side meets every set on the other. If H(d,k)<weightedMass(omega,C) and H(d,k)<weightedMass(omega,D), then card(C.slice(1))+(k+1)<=card(C.slice(d-1)) and card(D.slice(1))+(k+1)<=card(D.slice(d-1)). The two conclusions hold together. Neither positivity nor monotonicity of the weights is assumed; selected ranks or all ranks may have zero weight. The strict hypotheses exclude the all-zero case. For a finite set J in a larger ambient carrier, use its element subtype, as for the preceding theorem.

The mass estimate is a principal-filter count. If every member contains A and card(A)>=d-k, choose A0 contained in A with card(A0)=d-k. Every member is the complement of a subset B of the k-element complement of A0. For each j there are binom(k,j) such subsets of size j, whose complements have rank d-j. Nonnegativity bounds the mass by H(d,k), using Mathlib's powerset rank sum and powersetCard count. This step compares included sets, without comparing weights at different ranks.

For one direction write s=card(C.slice(1)) and t=card(C.slice(d-1)), and assume t<s+k+1. When s=0, t<=k. Let M be all labels whose complementary coatom is missing from C. Then card(M)=d-t>=d-k. Every member of C contains M: an omitted label of M would put that member below a missing coatom, contrary to upperness. The principal-filter bound contradicts C's strict mass hypothesis. When s=1, upperness supplies the d-1 coatoms containing the unique singleton, so t-s>=d-2>k, again impossible. When s>=2, each coatom contains a selected singleton and t=d. The small-gap assumption forces at least d-k singleton labels in C. Cross-intersection forces every member of D to contain all those labels, so D's principal-filter bound contradicts its strict mass hypothesis. Interchanging the families proves the second conjunct. Both upperness assumptions are used through these two directions; the partner's mass is essential.

The endpoints k=0 and k=d-3 are included, in particular d=3,k=0. The earlier gap-two theorem is the k=1 consequence for d>=4 and retains its original statement. Strictness cannot be replaced by weak mass inequalities: for unit weights choose card(A)=d-k, C all supersets of A and D all sets meeting A. They are cross-intersecting upper families; C has mass H(d,k)=2^k, D has mass 2^d-2^k, and C has gap k. The range cannot extend to k=d-2: a one-point star on both sides has unit mass 2^(d-1)>H(d,d-2)=2^(d-2), but gap d-2 rather than d-1. A large first-side mass alone likewise gives no such conclusion. This is a repository derivation; no literature priority, sharp polygon bound or attainment is asserted.

Conditional ordinary application to n=24. Retain the original domain of B-33, B-37 and B-41 in the intrinsic-classification-and-polygon-geometry theory source: an arbitrary labelled strictly convex 24-gon; any six distinct pairwise compatible actual ears D={f_ab} labelled by E(K4), allowing shared endpoints; any four prescribed actual triangulations T_a with complete Ear(T_a)=S_a={f_ab:b!=a}; and any family F containing these witnesses and intersecting on full actual ear sets. Gamma(H) contains every actual triangulation with exact D trace H, with every outside-D ear and every distinct completion retained. The following inference is conditional on the complete B-37/B-41 compression, counting, fullness and loss chains. This generic Lean theorem alone does not compile those chains or certify an end-to-end n24 maximum or classification. B-47 of the same-parity-deficit volume treats n=23; it does not already contain this n24 consequence.

Use M1={f12,f34}, M2={f13,f24}, M3={f14,f23}, and Q_i=D minus M_i. For each pair i!=j take P=M_i, Q=M_j, K=P union Q. The two original sides are F intersect X(P|Q) and F intersect X(Q|P); they contain their respective cores, are disjoint as actual triangulations, and their cardinalities sum to the original z_ij. All common ears lie in E_K, the full set of ears outside K compatible with each ear of K. It includes the third matching and compatible outside-D ears, and is not restricted to ears compatible with all six D ears. B-37.2's local delete/restore maps preserve the forced and forbidden sets separately on each side. Its maximal cross-pair replacement and projection preserve cross-intersection and do not decrease either mass. They yield a common compatible J subset E_K and upper cross-intersecting families C,D. Each pair may have a different J. Nonempty cross-intersection gives d=card(J)>=1, and compatibility of J union K gives d+4<=12, hence d<=8. No fixed K is required to attain eight, and no parity, symmetry, saturation, protection carrier or common compression carrier is imposed.

Put c_r=Catalan(22-r), V_r=c_(r+2)-2*c_(r+3)+c_(r+4), and omega_r^(d)=sum(j=0,...,d-r) (-1)^j*binom(d-r,j)*V_(r+j). Forcing r selected J ears and P, excluding Q, then excluding the unselected observed J ears gives precisely these complete actual fiber counts. Unobserved ears stay free. Swapping the sides gives the same weights because card(P)=card(Q)=2. The largest c index is d+4<=12, leaving at least twelve vertices in each count. B-37/B-41's conditional flip injections give nonnegative decreasing weights and G_d=omega_0^(d)-omega_d^(d)>0, decreasing with d. With alpha_r=card(C.slice(r))/binom(d,r), upperness gives increasing alpha_r, and cross-intersection gives alpha_0=0, alpha_d=1 and disjointness of the complement image of C from D. Consequently the original deficit d_ij=s-z_ij is at least sum(0<=r<d/2) binom(d,r)*(omega_r^(d)-omega_(d-r)^(d))*(alpha_(d-r)-alpha_r). All terms are nonnegative; r=0 contributes G_d and r=1 contributes (omega_1^(d)-omega_(d-1)^(d))*(card(C.slice(d-1))-card(C.slice(1))).

Here s=3507232740 and T=V_6=1396652. Exact integer evaluation gives H(6,0)=1396652, H(7,1)=1010990+385662=1396652, and H(8,2)=732564+2*278426+107236=1396652. If original core sizes a_i,a_j>T, each original side, hence each compressed mass, is greater than T. Apply the theorem at (d,k)=(6,0),(7,1),(8,2). The corresponding G_d values are 539668320,396434720,291031620; the rank-one minus coatom weight differences are 193270840,143233600,105403100. Thus d_ij is at least 732939160,682901920,607240920 respectively. For d<=5 retain G_d>=G_5=732939160. Every active pair has the basic bound G_d>=G_8=291031620, and every pair with both cores above T has d_ij>=607240920. These omega differences are dimension-specific conditional weights, not the original six-ear trace weights w_r.

All losses belong to the same original F. In B-37 notation set eta=u0-u, r_i=w4-b_i, ell_i=2*w3-t_i and d_ij=s-z_ij, where a_i,b_i,t_i,u,z_ij are the original exact-trace counts. The unchanged identities are card(F)-L=a_k-(eta+r_k+ell_i+ell_j+d_ij) and 2*(card(F)-L)=h-2*eta-sum_i ell_i-sum_(i<j) d_ij, with L=12909891720 and h=w2-w4=1623971580. When all three cores are active, B-37.7 gives eta>=0,r_i>=1,ell_i>=2 from original fullness obstructions and complete-ear realizations, without A>W. If some a_k<=T, the first identity gives card(F)-L<=1396652-5-291031620=-289634973, hence card(F)<=12620256747. If all a_i>T, the second gives 2*(card(F)-L)<=1623971580-6-3*607240920=-197751186, hence card(F)<=12811016127=L-98875593<L. These exhaust the three-active-core case. The pair estimates all bound losses of this same F; their combination does not assert simultaneously attained marginal optima or simultaneous compressions.

Conditionally consuming the remaining original B-33.3/B-37.3/B-37.5/B-37.9 chains, the original residual domain consists of allowed F with all a_i>0 and A>w2. Its finite maximum is below L when nonempty; its value is defined as zero when empty. Thus the ordinary inference gives K0=max(L,K_res)=L and transfers the existing twelve labelled full-fiber equality families, without a symmetry quotient. Explicitly, let U0={S1,S2,S3,S4} union (binom(D,4) minus {Q1,Q2,Q3}) union binom(D,5) union {D}. Choose i, order the other indices j<k, and independently for each x in M_i choose E_x from {M_j union {x}, M_k union (M_i minus {x})}. The trace family is B_(i,E)=U0 union {M_i,Q_j,Q_k} union {M_i union {z}:z in D minus M_i} union {E_x:x in M_i}; the actual family is the union of Gamma(H) over H in B_(i,E). The cited realization and full-fiber equality chains supply attainment, distinction and exhaustion for the arbitrary fixed four witnesses. This paragraph is conditional ordinary mathematics, not a kernel-verified polygon classification. No residual inhabitation, sharpness or attainment of the three-core bound, n>=25 conclusion, or completion of the larger FIB goal follows from this generic unit.

## Generic weighted product comparison

This application uses the preceding weightedMass definition and existing Mathlib suppliers. Let alpha be an arbitrary finite type with decidable equality, d=card(alpha), including d=0, and let w be a real radial weight function. Assume w_r>=0 for 0<=r<=d, Z=sum(r=0,...,d) binom(d,r)*w_r>0, and w_(r+1)<=R*w_r for every r<d. Weights outside these ranks are irrelevant. Individual weights may vanish, including a terminal string of zeros; the law need not be a product law. For any family E of subsets of this one carrier, define nu(E)=weightedMass(w,E)/Z. Finset.sum_powerset_apply_card identifies Z with sum(A subset alpha) w_card(A), so nu({A})=w_card(A)/Z and nu is a probability law.

For t in [0,1], let mu_t be the independent Bernoulli subset law: mu_t(E)=sum(A in E) t^card(A)*(1-t)^(d-card(A)), with the usual value 0^0=1. This is the real event mass of ProbabilityTheory.setBernoulli Set.univ t. Finite subsets and sets correspond by A maps to its underlying set, with inverse S maps to S.toFinset; E becomes the event {S : S.toFinset in E}. ProbabilityTheory.setBernoulli_real_singleton supplies the atom formula, and Fintype.sum_pow_mul_eq_add_pow gives total mass one. An upper event contains every superset of each of its members.

Fix q=13/18, p=q^4=28561/104976 and R=p/(1-p)=28561/76415. These constants lie strictly between zero and one, R>0 and p+q<1. For every upper E the comparisons are nu(E)<=mu_p(E) and mu_q(E)<=nu({A : complement(A) in E}). Complements here are taken inside alpha. The second right-hand event is the reflection flip(E) of E under complementation of each subset; it is not the event complement E^c consisting of subsets outside E.

To derive the first comparison, divide adjacent decay by positive powers of R. The odds score r maps to w_r/R^r is antitone on ranks 0,...,d; Fin.antitone_iff_succ_le supplies precisely this passage from successive inequalities. Since card(A intersect B)<=card(A) and card(A union B)+card(A intersect B)=card(A)+card(B), the score inequality gives w_card(A)*R^card(B)<=w_card(A intersect B)*R^card(A union B). The cardinality identity is Finset.card_union_add_card_inter.

Put f(A)=w_card(A)/Z and g(A)=p^card(A)*(1-p)^(d-card(A))=(1-p)^d*R^card(A). The preceding inequality, multiplied by (1-p)^d/Z, is the mixed Holley condition f(A)*g(B)<=f(A intersect B)*g(A union B). Both functions are nonnegative and sum to one. Applying Mathlib holley from Combinatorics.SetFamily.FourFunctions to the monotone nonnegative indicator of E yields sum(A in E) f(A)<=sum(A in E) g(A), exactly nu(E)<=mu_p(E). This is a comparison between f and g; no product structure, log-supermodularity, or strict positivity of the actual weights w is assumed.

## Independent intersection and complement reflection

For all u,v in the closed interval [0,1], the entire joint law satisfies (mu_u product mu_v).map((A,B) maps to A intersect B)=mu_(u*v). This is equality of probability measures, for every event, before imposing upperness. Draws A and B are independent, and the membership coordinates within each draw are independent. At each coordinate, the conjunction of independent Bernoulli predicates with parameters u,v has parameter u*v; different coordinates retain independence.

The supplier correspondence uses ProbabilityTheory.setBernoulli_eq_map and MeasureTheory.Measure.infinitePi_eq_pi to express subsets as finite products of Bernoulli predicates. ProbabilityTheory.bernoulliMeasure_real_apply computes the two coordinate outcomes. MeasureTheory.measurePreserving_arrowProdEquivProdArrow regroups the product of two coordinate arrays as an array of independent pairs, and MeasureTheory.Measure.pi_map_pi transports coordinate conjunctions. MeasureTheory.Measure.map_prod_map and MeasureTheory.Measure.map_map compose these identifications. They give the whole pushforward equality, with the Set/Finset event correspondence above preserving the same intersection operation.

If E is upper, A intersect B in E forces both A in E and B in E. Thus the intersection preimage of E is contained in E product E; the joint equality and MeasureTheory.measureReal_prod_prod give mu_(u*v)(E)<=mu_u(E)*mu_v(E). Applying this first at (u,u) and then at (u^2,u^2), using nonnegative event masses, gives mu_(u^4)(E)<=mu_(u^2)(E)^2<=mu_u(E)^4. In particular mu_p(E)<=mu_q(E)^4.

To obtain the literal reflected comparison, note that flip(E) is lower when E is upper, so the event complement (flip(E))^c is upper. The first comparison gives nu((flip(E))^c)<=mu_p((flip(E))^c). Complementing event masses and using mu_p(flip(E))=mu_(1-p)(E) gives mu_(1-p)(E)<=nu(flip(E)). Since q<1-p, independently thin a mu_(1-p) draw by a mu_t draw with t=q/(1-p)=75816/76415 in [0,1]. The joint intersection law gives parameter q; upperness and intersection contained in the first draw give mu_q(E)<=mu_(1-p)(E). Consequently mu_q(E)<=nu(flip(E))=nu({A : complement(A) in E}), in the required direction.

The joint law and upper-event inequality include u=0 or v=0, when the intersection is surely empty, and u=1 or v=1, when its law is the other draw. The suppliers ProbabilityTheory.setBernoulli_zero and ProbabilityTheory.setBernoulli_one express these endpoint laws. On the empty carrier every Bernoulli law is the point mass at the empty subset; Z=w_0>0 makes nu the same point mass. The empty event has mass zero and the full event has mass one under either law. No positive lower cutoff for both cross-intersecting families can hold on an empty carrier.

Identical marginals cannot replace the independent product. If B=A is the same random draw, both marginals are mu_u but A intersect B=A has law mu_u. On a one-point carrier with u=1/2, the full subset has intersection probability 1/2 for these identical draws and 1/4 for independent draws. For a fixed-coordinate event {A : i in A}, independent draws attain equality mu_(u*v)(E)=u*v=mu_u(E)*mu_v(E). For the nonprincipal upper event of nonempty subsets of a two-point carrier at u=v=1/2, the inequality is strict: mu_(1/4)(E)=7/16<9/16=mu_(1/2)(E)^2.

## Cross-intersecting masses and the two quartic curves

Let C,D be upper families on this same alpha, and require every A in C to meet every B in D. Set x=nu(C) and y=nu(D). Nonnegative weights and total Z give 0<=x,y<=1. Literal cross-disjointness is C intersect flip(D)=empty: membership would put A in C and complement(A) in D, whose intersection is empty. Thus x+nu(flip(D))<=1. Swapping the two families likewise gives y+nu(flip(C))<=1. These are event disjointness statements under the same normalized law, not assertions about independently selected actual polygon objects.

Reflection now gives mu_q(C)<=nu(flip(C))<=1-y and mu_q(D)<=nu(flip(D))<=1-x. For C, comparison and the fourfold bound yield x<=mu_p(C)=mu_(q^4)(C)<=mu_q(C)^4<=(1-y)^4. Interchanging C,D gives y<=(1-x)^4. Nonnegativity of the event masses and of 1-x,1-y justifies the fourth-power directions. Both curves are obtained together for this pair on its one carrier.

## Strict scalar gap with either two-sided cutoff

Under both non-strict lower bounds x,y>=1/256, the two quartic curves imply x+y<5/6. Separately the same strict conclusion holds under both non-strict bounds x,y>=(23/100)^4=279841/100000000. Neither statement requires a strict lower cutoff. Here is the scalar derivation, which uses no carrier dimension assumption.

For either a=1/256 or a=279841/100000000, assume a<=x,y<=1 and both quartic curves, and suppose x+y>=5/6. By symmetry take x<=y. If x>5/12, then y>=x>5/12 and 0<=1-y<7/12, so x<=(1-y)^4<=(7/12)^4<5/12, a contradiction. Therefore x<=5/12. The assumed sum gives y>=5/6-x, hence 0<=1-y<=x+1/6, and the first curve forces x<=(x+1/6)^4.

Write t=x+1/6. Then t lies in [a+1/6,7/12], and phi(t)=t^4-t+1/6=t^4-x>=0. The function phi is convex on the nonnegative real axis: use convexOn_pow 4, subtract the affine identity, and add the constant 1/6. ConvexOn.le_on_segment bounds phi(t) by the maximum of its endpoint values. The right value is phi(7/12)=-6239/20736<0. For a=1/256 the left value is phi(131/768)=(131/768)^4-1/256<0; for a=279841/100000000 it is phi(50839523/300000000)=(50839523/300000000)^4-279841/100000000<0. Indeed, for either a, a+1/6<=131/768<23/100 and (23/100)^4<=a, so (a+1/6)^4<a. Both endpoints are strictly negative even when x or y equals a. Convexity contradicts phi(t)>=0, proving the strict sum bound in each case.

Both lower cutoffs are essential. On d=7 take the Bernoulli product law of parameter 1/4, with radial weights w_r=(1/4)^r*(3/4)^(7-r) and Z=1. Its adjacent ratio is 1/3<=R. Let C be all nonempty subsets and D consist only of the full subset. They are upper and cross-intersecting, and their masses x=1-(3/4)^7, y=(1/4)^7 satisfy both quartic curves. The first mass meets either cutoff, the second meets neither, and x+y=7099/8192>5/6. Swapping C,D shows that either one-sided omission invalidates the conclusion.

## Nonproduct weights and the actual polygon boundary

For a genuinely nonproduct law take d=3 and rank weights (1,R,R^2/2,0). They are nonnegative, have positive total Z=1+3*R+3*R^2/2, satisfy the adjacent bounds, and have a zero top weight. The identity w_1^2=w_0*w_2 fails. Indeed two distinct singletons give w_1^2>w_0*w_2, so actual-weight log-supermodularity is unavailable. For E={A : card(A)>=2}, nu(E)=(3*R^2/2)/(1+3*R+3*R^2/2)<3*p^2*(1-p)+p^3=mu_p(E). In contrast weights w_r=R^r normalize to mu_p and attain equality in the first comparison.

Upperness, adjacent decay and the reflection parameter restriction have separate roles. On d=1, weights (1,0) meet decay but the non-upper event {empty subset} has nu mass 1>1-p. Weights (0,1) violate decay and give the upper full-subset event nu mass 1>p. For product weights R^r on d=1, replacing q by 4/5 makes p+4/5>1 and the reflected mass of the fixed-coordinate upper event is 1-p<4/5, reversing the desired comparison. These failures do not exclude zero tails or nonproduct weights under the stated hypotheses.

For the original polygon consumer the candidate actual rank weights are w_r=Npq(n,r+2,d-r+2), with Npq from D5.S3.Geometry.Polygons.PolygonConditionalCounts and the integer counts viewed as real weights. Using them here requires proofs of the exact trace-to-forced/forbidden count correspondence, legality of the carrier and d, nonnegativity and positive total with the correct partition normalization, actual adjacent decay, both actual lower cutoffs, and deficit transfer for the same original F. The displayed generic probability calculation does not discharge those bridges. Pairwise compressed carriers may differ across the three pairs; each C,D comparison needs a single common carrier only within its own pair.

The original domain remains every labelled strictly convex n-gon with n>=14, six distinct pairwise compatible actual ears labelled f_ab by E(K4), four prescribed actual triangulations T_a with complete Ear(T_a)=S_a={f_ab:b!=a}, allowing shared endpoints among ears, and one family F intersecting on full actual ear sets. All three active cores, all completions, outside ears and completion multiplicities remain in scope. Combining bounds requires losses of that same F; independent Bernoulli draws used for the comparison do not assert joint realizability or independence of polygon fibers, or simultaneous attainment of separate pair optima. This exposition supplies an application of existing declarations, with no new general theorem or literature priority claim. It proves no full polygon result, n=47 result, unbounded polygon range, or completion of the larger FIB goal.

## References

- Truth anchor: `D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap.weightedMass`
- Truth anchor: `D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap.weighted_cross_intersecting_layer_gap`
- Truth anchor: `D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap.weighted_cross_intersecting_layer_gap_of_binomial_threshold`
