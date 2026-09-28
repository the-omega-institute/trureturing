# Critical opposite floors and a mixed six-valent star

## Abstract

A six-occurrence critical edge has strict angle-sum margins on both continuous faces, allowing two transition occurrences.

I is an arbitrary finite type of cardinality six. The five functions y,z,o,v,w:I -> Real retain every local occurrence. The target coordinate is shared. At each occurrence the order is (12,13,14,34,24,23); o is opposite the target and y,z,v,w are its four neighbours. All five coordinates lie in [1,2]. ThreeSmall means at least three of the four neighbours are at most 5/4, expressed as the four possible conjunctions.

good is a finite subset of I with at least four members. At every good occurrence all four neighbours are at most 5/4 and o is at least 4/3. No equality of the target and opposite, no prescribed angle and no angle-sum inequality is a hypothesis. AngleSum(a,y,z,o,v,w) below abbreviates the sum over i:I of arccos(cosine(a,y(i),z(i),o(i),v(i),w(i))). cosine is the original six-variable expression from FourCycleEnvelopes, not a free function.

Define beta=arccos(49/sqrt(6534)), gamma=arccos(43/99), and margin=min(2pi-6arccos(4/7),4gamma+2beta-2pi). These are exactly the three definitions in the paired Lean source.

**Theorem 1.1 (Both boundary sums have the same positive margin).**

$$\forall I \in Type, y \in I \to Real, z \in I \to Real, o \in I \to Real, v \in I \to Real, w \in I \to Real, good \in Finset\left(I\right),\; \left(Fintype\left(I\right) \land \left(Fintype.card\left(I\right) = 6 \land \left(4 \le Finset.card\left(good\right) \land \left(\left(\forall i \in I,\; y\left(i\right) \in Icc\left(1, 2\right) \land \left(z\left(i\right) \in Icc\left(1, 2\right) \land \left(o\left(i\right) \in Icc\left(1, 2\right) \land \left(v\left(i\right) \in Icc\left(1, 2\right) \land w\left(i\right) \in Icc\left(1, 2\right)\right)\right)\right)\right) \land \left(\left(\forall i \in I,\; ThreeSmall\left(y\left(i\right), z\left(i\right), v\left(i\right), w\left(i\right)\right)\right) \land \left(\forall i \in I,\; i \in good \Rightarrow \left(y\left(i\right) \le \frac{5}{4} \land \left(z\left(i\right) \le \frac{5}{4} \land \left(v\left(i\right) \le \frac{5}{4} \land \left(w\left(i\right) \le \frac{5}{4} \land \frac{4}{3} \le o\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(0 < margin \land \left(AngleSum\left(\frac{4}{3}, y, z, o, v, w\right) \le sub\left(mul\left(2, pi\right), margin\right) \land add\left(mul\left(2, pi\right), margin\right) \le AngleSum\left(2, y, z, o, v, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/CriticalTransitionStar.critical_transition_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reuse the derivative-based mixed comparison from the single analytic owner. The lower target 4/3 gives cosine at least 4/7. At target 2 the four possible three-small-neighbour endpoints each give squared cosine 2401/6534. Four small neighbours and opposite floor 4/3 give exactly 43/99. Denominator positivity and square-root comparison are proved within the source.

For gamma in [0,pi/2], cos(2gamma)=-6103/9801. The positive square comparison (6103/9801)^2-2401/6534=3896615/192119202 proves 2gamma>pi-beta. This gives 4gamma+2beta>2pi. The lower gap follows from 4/7>cos(pi/3). Summing beta plus the good-occurrence increment gamma-beta, and using card(good)>=4, gives the actual six-occurrence upper-face bound. It is not a theorem with the desired budget assumed.

The quantified functions vary over continuous faces. Pullbacks of one shared global length vector are included among these functions; the source does not construct the global incidence carrier or prove manifold links, co-volume existence or the full CFMP conjecture. The ordinary application uses favourable opposites of the same degree class, so it is preserved by unbranched covers even when global edge identities split. The statement itself does not certify the cover construction or its geometric realization.

**Remark 1.2 (Written continuation: flat pairs constrain shared lengths).**

$$
\forall ell \in PositiveLengths, q \in OppositePairs,\; FlatAt\left(ell, q\right) \Rightarrow add\left(1, add\left(MeanCosh\left(ell, OtherPairOne\left(q\right)\right), MeanCosh\left(ell, OtherPairTwo\left(q\right)\right)\right)\right) \le MeanCosh\left(ell, q\right)
$$

*Source.* Repository-derived.

*Acknowledgement.* trureturing contributors (2026). *Sources for critical six-valent transition stars and cover-stable realization*. URL: <https://raw.githubusercontent.com/the-omega-institute/trureturing/8009ec61bf9a08f36a96f37f0f666bc4e0b45da3/docs/develop/theory/CFMP_GEOMETRIC_REALIZATION.md>.

*Commentary.*

This authored Remark records written mathematics beyond critical_transition_star. It names no new Lean declaration and does not enlarge that theorem's kernel-certified statement. PositiveLengths denotes the six positive original edge lengths; OppositePairs consists of the three unordered pairs of opposite local edges. FlatAt(ell,q) means that the extended hyperideal angles are pi on q and zero on the other four edges. MeanCosh(ell,q) is cosh of the arithmetic mean of the two LENGTHS in q. OtherPairOne and OtherPairTwo denote the remaining two opposite pairs, in either order.

Luo-Yang Corollary 4.12 supplies the C1 convex extended co-volume whose gradient is the extended angle vector. Subtracting the flat angle vector's linear functional makes its fixed-gradient fibre a convex minimizer set. The tetrahedral Klein four group preserves that flat angle vector. Its length average is (u,v,w,u,v,w). With X=cosh(u),Y=cosh(v),Z=cosh(w), the original cosine satisfies phi+1=(X+1)*((Y+Z)^2-(X-1)^2)/D, where D=X^2+Y^2+Z^2+2XYZ-1>0. This proves the displayed necessary inequality. The local average is not assumed to be an admissible global length modification. Equivalence is asserted only for opposite-pair-equal length vectors.

Actual global edge-pair multisets must share the same MeanCosh value. A flat candidate points from its pi pair to its two zero pairs and forces strict decrease, so directed cycles are impossible. A pi pair AB with zero pairs AA and BB is also excluded by convexity of cosh. Consequently, with exactly two global edges, each occurring at least twice in every tetrahedron, mixed pi pairs are impossible. A pure pi pair saturates one global edge and contradicts any genuine tetrahedron. The strict angle construction and the cited maximizer theorem therefore give realization under minimum degree six in the strict boundary setting. The three-tetrahedron example has degrees six and twelve and one genus-two boundary.

The same bound gives the sharp all-geometric interval criterion cosh(M)<1+2cosh(m) for 0<m<=M, and the genuine positive cosh cube (1,3]^6. It does not extend the old neighbour-monotonicity domain: an explicit genuine point has a negative neighbour derivative. General CFMP, arbitrary one/five local label patterns, and completeness of the flat-candidate elimination remain outside these conclusions. The source note credits the existing small-manifold census; this example is not asserted to be a new homeomorphism type. No compilation or projection receipt for this new Remark is claimed here.

**Remark 1.3 (Written continuation: two global edges and two-flat support).**

$$
\forall T \in StrictBoundaryTriangulations,\; \left(MinimumDegreeSix\left(T\right) \land EdgeCount\left(T\right) \le 2\right) \Rightarrow GenuineRealization\left(T\right)
$$

*Source.* Repository-derived.

*Acknowledgement.* trureturing contributors (2026). *Sources for critical six-valent transition stars and cover-stable realization*. URL: <https://raw.githubusercontent.com/the-omega-institute/trureturing/8009ec61bf9a08f36a96f37f0f666bc4e0b45da3/docs/develop/theory/CFMP_GEOMETRIC_REALIZATION.md>.

*Commentary.*

This is an authored written-mathematics Remark, not a new Lean declaration or an extension of critical_transition_star. StrictBoundaryTriangulations means finite connected orientable actual face-paired ideal triangulations with every vertex link a closed surface of genus at least two. MinimumDegreeSix counts local edge occurrences. EdgeCount counts actual global edge equivalence classes. GenuineRealization means a nondegenerate hyperbolic metric on that same triangulation with totally geodesic boundary. No local two/four label quota is a premise below.

For actual cosh coordinates (r,a,b,o,c,d)>1, the two cosine radicands are squared norms of the Cauchy vectors written in the source note. Their nonnegative remainder J gives the exact flat condition (r-1)(o-1)>=(sqrt(ac)+sqrt(bd))^2+J. Equality J=0 holds exactly at a=c,b=d. The necessary product gap sqrt(ro)>=1+sqrt(ac)+sqrt(bd) is distinct from the previous cosh-of-mean bound. It is not asserted to be sufficient.

The existing strict-angle construction and the cited Luo-Yang maximizer theorem give common positive generalized lengths and at most EdgeCount-1 flat blocks. With two edges a remaining unique flat must have five A cosh coordinates and one B, with B>4A+5. Every other B-containing block has at least two B occurrences. The nine continuous local graph estimates make their total B angle exceed pi/4 per occurrence, contradicting the global 2pi sum. The (6,18) four-tetrahedron packet explicitly has singleton-label blocks outside the earlier local quota.

There is a further result without restricting the total global edge count: if minimum degree is six, at least one block is genuine and at most two are flat, the pi slots use pairwise distinct global labels. A saturated label is confined to the flat blocks. Exact face signatures leave only single/five or star/star supports. Face connectivity excludes the first; matching the unique longest nonstar edge excludes the second by strict shared length order or a degree-two contradiction. Thus three global edges leave at most one flat block. If all actual label types occur at least twice, none can be flat.

The four-tetrahedron witness is not a newly claimed census type. The positive arccosh(3) cube is already Feng-Ge-Hua Theorem 3.9. No new kernel, Scribe compilation, projection or independent review receipt is asserted. Full CFMP, an isolated flat using three independent lengths, and larger flat sets remain outside the displayed conclusions.

**Remark 1.4 (Written colouring continuation: states, parity and interfaces).**

$$
\forall T \in StrictBoundaryTriangulations, ell \in GlobalLengthVectors\left(T\right),\; \left(PositiveGeneralizedLengths\left(T, ell\right) \land \left(ZeroEdgeCurvature\left(T, ell\right) \land SaturatedDegreeAtLeastThree\left(T, ell\right)\right)\right) \Rightarrow SaturatedEdgeCount\left(T, ell\right) \le MismatchedFlatFaceCount\left(T, ell\right)
$$

*Source.* Repository-derived.

*Acknowledgement.* trureturing contributors (2026). *Sources for critical six-valent transition stars and cover-stable realization*. URL: <https://raw.githubusercontent.com/the-omega-institute/trureturing/8009ec61bf9a08f36a96f37f0f666bc4e0b45da3/docs/develop/theory/CFMP_GEOMETRIC_REALIZATION.md>.

*Commentary.*

This authored research Remark is separate from the original Lean declaration. StrictBoundaryTriangulations has the existing actual finite orientable face-pairing meaning. PositiveGeneralizedLengths means one positive original length per global edge; ZeroEdgeCurvature means every occurrence-counted angle sum is 2pi. SaturatedDegreeAtLeastThree requires degree at least three at every edge carrying two pi occurrences.

A flat state is one of the three unordered 2+2 vertex partitions. The two within-class edges carry pi, the four cross-class edges zero. A flat tetrahedron marks one edge in each triangular face. MismatchedFlatFaceCount counts paired flat/flat faces once when their marked edge occurrences disagree under the actual face map. This does not assert a mismatch of the faces' intrinsic metrics.

SaturatedEdgeCount counts actual global edges with two pi occurrences. Such an edge has no genuine occurrence and its binary normal cycle has at least two status changes. One mismatched face accounts for exactly two changed edge slots, with repeated labels counted as occurrences. Summing proves the displayed inequality without bounding the number of flat tetrahedra.

Rainbow global three-edge colours require all edge degrees to be even. If degrees are constant within each colour and their reciprocals sum to less than one half, the classical hyperideal angle existence and uniqueness theorem constructs a genuine shared metric. For the triple six,six,eight, cosh-lengths are 2+3sqrt(2)/2, 2+3sqrt(2)/2, 2+sqrt(2). A completely specified 48-tetrahedron group construction gives four genus-two boundary components.

Taut and veering structures are credited combinatorial frameworks, not automatic hyperideal geometric realizations. The known nine-degree P4 example cannot have rainbow three-edge colours. No new formal theorem, compilation or projection receipt, complete CFMP proof, or mathematical-priority claim accompanies this Remark.

**Remark 1.5 (Written continuation: every flat set exposes a pi edge).**

$$
\forall T \in StrictBoundaryTriangulations, ell \in GlobalLengthVectors\left(T\right),\; \left(PositiveGeneralizedLengths\left(T, ell\right) \land \left(ZeroEdgeCurvature\left(T, ell\right) \land \left(MinimumDegreeSix\left(T\right) \land HasFlat\left(T, ell\right)\right)\right)\right) \Rightarrow Nonempty\left(ExposedPiEdges\left(T, ell\right)\right)
$$

*Source.* Repository-derived.

*Acknowledgement.* trureturing contributors (2026). *Sources for critical six-valent transition stars and cover-stable realization*. URL: <https://raw.githubusercontent.com/the-omega-institute/trureturing/8009ec61bf9a08f36a96f37f0f666bc4e0b45da3/docs/develop/theory/CFMP_GEOMETRIC_REALIZATION.md>.

*Commentary.*

This authored research Remark records ordinary written mathematics and names no new Lean declaration. T ranges over actual finite orientable face-paired ideal triangulations in the existing strict boundary setting. PositiveGeneralizedLengths assigns one positive original length to every actual global edge. ZeroEdgeCurvature requires the occurrence-counted sum at each global edge to be 2pi. MinimumDegreeSix counts occurrences.

FlatSet is the entire set of flat tetrahedra under this same generalized length vector. For each global edge e, m(e) counts its pi slots in FlatSet and n(e) counts all its flat slots. ExposedPiEdges consists of those with m(e)=1 and n(e) equal to one or two. HasFlat means FlatSet is nonempty. The displayed conclusion asserts this exact exposed set is nonempty, with no bound of two on the number of flat tetrahedra and no colouring premise.

The existing Cauchy remainder and AM-GM give, for flat cosh coordinates (r,a,b,o,c,d) with selected pair r,o, 2log(r)+2log(o)-log(a)-log(b)-log(c)-log(d)>log(16). Summing uses the shared value w(e)=log(cosh(ell(e)))>0 and coefficient 3m(e)-n(e). At m=2 saturation forces n=degree>=6; at m=0 the coefficient is nonpositive. Only the exposed edges can provide the necessary positive sum. Their cosh products satisfy product x(e)^(3-n(e))>16^card(FlatSet), hence product x(e)>4^card(FlatSet). The complete positive correction terms are retained in the written theory.

Every exposed edge has at least four genuine local occurrences, with angle sum exactly pi and at least one angle at most pi/4. These occurrences need not be distinct tetrahedra. The pi-selection multigraph has one edge per flat tetrahedron and graph degree m(e)<=2. Its path count p obeys v_pi=f+p. Each flat-only face component requires a different path component by the same signed budget and saturated normal circle argument, so f<=v_pi-c_F. Cycle components can remain.

Luo-Yang Lemma 4.3 defines each positive face-corner truncation length from the shared original face lengths. A flat corner's longest side is at least the sum of the two others. Following longest sides through mismatched flat faces strictly increases this shared length. A closed all-mismatch corner walk is impossible; genuine blocks and compatible flat faces are allowed terminal states. The two local cosh vectors (2,2,2,20,2,2) and (2,2,2,2,20,2), sharing face123, exhibit a legal local mismatch. They are not a complete CFMP instance.

These are necessary conditions, not a proof that the small genuine angles or large exposed lengths cannot occur. The original critical_transition_star statement and Lean source are unchanged. No Scribe compilation or projection, new kernel certification, independent referee approval, full CFMP proof or counterexample is represented by this Remark.

**Remark 1.6 (Written continuation: endpoint caps and unequal transverse pairs).**

$$
\forall a \in GenuineHyperidealAngles, e \in TetrahedronEdges,\; EndpointSumsAtMostHalfPi\left(a, e\right) \Rightarrow CoshOriginalEdgeLength\left(a, e\right) < 3
$$

*Source.* Repository-derived.

*Acknowledgement.* trureturing contributors (2026). *Sources and scope for the CFMP mixed-matching continuation*. URL: <https://github.com/the-omega-institute/trureturing/pull/9474>.

*Commentary.*

This authored Remark describes ordinary written mathematics, not a new Lean declaration. GenuineHyperidealAngles is the six positive dihedral angles with each vertex sum below pi. TetrahedronEdges is the six local edges. EndpointSumsAtMostHalfPi(a,e) requires the sums of the three angles at EACH endpoint of e to be at most pi/2. CoshOriginalEdgeLength(a,e) is the actual angle-to-length formula, whose denominator reads endpoint vertex triples, not face triples. No equality between angles or lengths is assumed.

More generally, endpoint caps sigma1,sigma2<=pi/2 imply ell(e)<asinh(tan(sigma1/2))+asinh(tan(sigma2/2)). Cauchy-Schwarz in the positive matrix [[1,cos(theta)],[cos(theta),1]], followed by D=(cos(theta)+cos(a+b))*(cos(theta)+cos(a-b)), proves the bound. At equal cap sigma the sharp cosh supremum is (3-cos(sigma))/(1+cos(sigma)). The genuine angle family (sigma-2eps,eps,eps,eps,eps,eps) approaches it. Frigerio-Moraschini Section 1.1 and Luo-Yang Section 6.1 supply the classical inverse formula; they are not claimed as new results.

A separate window with target and three adjacent angles at most pi/5 and the fourth at most pi/3 gives cosh(ell) <sqrt(237620/28431)<3. The endpoint determinant bounds are 243/125 and 117/100, and the numerator is less than 109/25. Either bound can certify genuine occurrences of the two pi labels of a proposed flat. Shared lengths below three then contradict the existing flat requirement (r-1)*(o-1)>4. Such qualifying witnesses are not automatically supplied by minimum degree.

The actual four-class patterns C=(R,A,B,R,A,B) and D=(R,A,B,S,A,B) have per-edge occurrence counts R:(p,q), A:(u,v), B:(h,k), S:(0,w), all parameters positive and degrees at least six. Counts imply pv=2qu and pk=2qh. Merging R,S gives a rainbow colouring, so actual oriented endpoint return forces even degrees. Typewise angle averaging preserves each edge equation; Luo-Yang and genuine D rigidity yield common R,A,B,S lengths without requiring A=B.

All three flat C states are excluded. Flat R forces p=1,q>=5,u and h even, so a genuine R occurrence has both endpoint sums at most 2pi/5 and R<3. Flatness requires R>=1+A+B>3. Flat A forces u=1,v odd,p divisible by four. The exact cosine difference gives sign(beta-delta)=sign(A-B), putting A in the four-small/one-medium window and contradicting A>3. The B branch interchanges the transverse classes.

The complete 22-tetrahedron packet has edge degrees 6,6,6,6,20,22,22,44, one genus-fifteen vertex link and counts (p,q,u,v,h,k,w)=(1,5,2,20,4,40,20). Its even face permutations are compatible with a specified alternating tetrahedron orientation. All sixteen link-vertex fans and oriented first returns are checked. The angle equations force A>B; connected cyclic covers yield an unbounded genuinely anisotropic family. The local caps need no role balance, but this global realization theorem still does. Full CFMP, new Lean certification, Scribe compilation or projection, CI, Freeze and independent review approval are not asserted.

**Remark 1.7 (Written continuation: coupled endpoint budgets without role averaging).**

$$
\forall T \in StrictBoundaryTriangulations,\; \left(MinimumDegreeSix\left(T\right) \land ThreeEdgesTwoSingletonLabels\left(T\right)\right) \Rightarrow GenuineRealization\left(T\right)
$$

*Source.* Repository-derived.

*Acknowledgement.* trureturing contributors (2026). *Sources and scope for the CFMP mixed-matching continuation*. URL: <https://github.com/the-omega-institute/trureturing/pull/9474>.

*Commentary.*

This is authored written mathematics, not a new Lean declaration. StrictBoundaryTriangulations means actual finite connected orientable face-paired ideal triangulations with every vertex link a closed surface of genus at least two. ThreeEdgesTwoSingletonLabels means the actual global edge set is exactly three distinct labels U,V,H, with U and V each occurring at most once in every tetrahedron. They may be absent. MinimumDegreeSix counts all actual local occurrences. GenuineRealization concerns the same prescribed triangulation. No role balance, equal angles, local templates or automorphism hypothesis is part of the displayed assertion.

For genuine angles (theta,a,b,g,c,d), put u=a+b,v=c+d. The exact half-angle form of the classical inverse formula proves cosh(ell12)<1+2sin(theta)^2/((cos(theta)+cos(u))*(cos(theta)+cos(v))). Both endpoints retain the same theta. For caps sigma1,sigma2<pi, m=min(sigma1,sigma2), M=max(sigma1,sigma2), the sharp supremum is 1+2(1-cos(m))/(cos(m)+cos(M-m)). A genuine small-epsilon family attains it in the limit. Frigerio-Moraschini supplies the inverse formula, not this claimed research derivation.

Logarithmic concavity gives a particularly useful consequence: the SUM of the two endpoint vertex-angle sums at most pi implies cosh(ell)<3. One endpoint may exceed pi/2. Every genuine occurrence of a common edge with cosh length at least three therefore needs 2*target_angle plus its four adjacent angles to exceed pi. Summing preserves actual neighbour multiplicities; they are not generally one. The separate individual-angle window allows the fourth neighbour to reach 7pi/15 when target and three neighbours are at most pi/5.

The strict-angle construction and Luo-Yang Theorems 1.4 and 6.3 give common positive generalized lengths. With three edges there are at most two flat blocks. Singleton U,V cannot saturate, and H occurs in every genuine block, so no label saturates and at most one flat remains. A selected singleton pi label then has at least five genuine occurrences. If its cosh length were at least three, they would demand more than 5pi; all actual available angles give at most 2pi+3pi. Thus the selected singleton cosh length is below three. Both possible types of pi pairs contradict the existing flat Cauchy product bound, proving the displayed realization.

Changing just (1,0;3,0;0132) to (1,0;3,0;0213) in the earlier eleven-block face table yields actual degrees 6,6,54 and one genus-nine vertex link. All three oriented first-return cycles and six link fans are checked. The unique (U,H,H,V,H,H) block prevents applying the earlier repeated-type criterion. Cyclic covers use metric lifting; their 3n edges do not satisfy the three-edge hypothesis when n>1.

DNA tetrahedron experiments motivate compatible paired data; they are not geometric proof inputs. Ge's 2026-09-23 preprint asserts existence of some geometric triangulation, which is distinct from realizing this prescribed triangulation. New numerical and finite checks supplement the written arguments. Full CFMP, independent review, new Lean certification, Scribe compilation/projection, CI and Freeze are not claimed.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/CriticalTransitionStar.critical_transition_star`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
