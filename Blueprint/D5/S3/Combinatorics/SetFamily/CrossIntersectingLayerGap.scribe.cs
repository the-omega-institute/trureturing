using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SetFamily;

internal sealed class CrossIntersectingLayerGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SetFamily/CrossIntersectingLayerGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative rank weights and cross-intersection force a gap between the coatom and singleton layers.",
        H("A Weighted Cross-Intersection Layer Gap"),
        Blocks(
            Describe.Lean(DescribeId.Create("cross-intersection-weighted-mass"),
                DeclarationHandle.Create(Prefix + "weightedMass"), H("Rank-weighted mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary finite carrier alpha and a finite family C of its subsets, "
                    + "weightedMass(omega,C) is the sum of omega(card(A)) over all A in C. "
                    + "The function omega assigns one real weight to each natural rank; "
                    + "the definition itself imposes no sign or monotonicity condition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weighted-cross-intersecting-layer-gap"),
                DeclarationHandle.Create(Prefix + "weighted_cross_intersecting_layer_gap"),
                H("The coatom layer exceeds the singleton layer by at least two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let alpha be any finite type with decidable equality, and put d=card(alpha). "
                        + "Assume d is at least four. Let omega be an arbitrary function from natural ranks to real numbers "
                        + "such that every weight is nonnegative. Zero weights are allowed, and no relation between "
                        + "weights at different ranks is required. Let C and D be finite families of subsets of alpha. "
                        + "Both families are upward closed under inclusion, and every member of C has nonempty "
                        + "intersection with every member of D. Suppose each family's weighted mass is strictly greater "
                        + "than omega(d-1)+omega(d). Then card(C.slice(1))+2 is at most card(C.slice(d-1)). "
                        + "Here slice(r) keeps exactly the members of cardinality r. "
                        + "The nonnegative weights and strict mass bounds also imply that both families are nonempty.")),
                    Paragraph(Text("For a finite set J in a larger ambient type, take alpha to be the subtype of elements "
                        + "of J. Its finite subsets are exactly subsets of J through the canonical inclusion. "
                        + "This identifies the statement for every finite J, with d=card(J), without choosing an ordering "
                        + "or restricting the original carrier to a particular labelled set.")),
                    Paragraph(Text("If every member of a family contains a fixed coatom, its only possible members "
                        + "are that coatom and the full carrier. Nonnegativity bounds its mass by the sum of the "
                        + "coatom and top weights. Thus an upward family above this threshold has at least two "
                        + "coatoms: with at most one missing-point index, every member would contain the corresponding coatom.")),
                    Paragraph(Text("Let t be the number of singletons in C. Cross-intersection forces every member "
                        + "of D to contain all t selected points. If t were at least d-1, every member of D would "
                        + "contain a fixed coatom, contradicting its strict mass bound. Hence t+2 is at most d. "
                        + "If t=0, the two-coatom bound proves the result. If t=1, upward closure includes at least "
                        + "d-1 coatoms, giving a gap of at least d-2, which is at least two. If t is at least two, "
                        + "every coatom contains a selected singleton, so all d coatoms belong to C and the result follows. "
                        + "The upward-closure hypothesis on D is retained in the statement, although this argument "
                        + "uses only its mass and cross-intersection.")),
                    Paragraph(Text("This theorem concerns arbitrary weighted families of finite subsets. "
                        + "Applying it to polygon completions requires a separate encoding of those completions, "
                        + "a proof that the resulting families satisfy these hypotheses, and any required compression "
                        + "or identification of families. Those constructions are outside this theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-cross-intersecting-variable-coatom-threshold"),
                DeclarationHandle.Create(Prefix + "weighted_cross_intersecting_layer_gap_of_binomial_threshold"),
                H("A binomial threshold forces the variable gap on both sides"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let alpha be any finite type with decidable equality, d=card(alpha), d>=3, "
                        + "and let k be any natural number with k<=d-3. For arbitrary real rank weights omega(r)>=0 "
                        + "define H(d,k)=sum(j=0,...,k) binom(k,j)*omega(d-j). Let C,D be upper families of subsets "
                        + "of alpha, cross-intersecting in the sense that every set on one side meets every set on "
                        + "the other. If H(d,k)<weightedMass(omega,C) and H(d,k)<weightedMass(omega,D), then "
                        + "card(C.slice(1))+(k+1)<=card(C.slice(d-1)) and "
                        + "card(D.slice(1))+(k+1)<=card(D.slice(d-1)). The two conclusions hold together. "
                        + "Neither positivity nor monotonicity of the weights is assumed; selected ranks or all ranks "
                        + "may have zero weight. The strict hypotheses exclude the all-zero case. For a finite set J "
                        + "in a larger ambient carrier, use its element subtype, as for the preceding theorem.")),
                    Paragraph(Text("The mass estimate is a principal-filter count. If every member contains A and "
                        + "card(A)>=d-k, choose A0 contained in A with card(A0)=d-k. Every member is the complement "
                        + "of a subset B of the k-element complement of A0. For each j there are binom(k,j) such "
                        + "subsets of size j, whose complements have rank d-j. Nonnegativity bounds the mass by "
                        + "H(d,k), using Mathlib's powerset rank sum and powersetCard count. This step compares "
                        + "included sets, without comparing weights at different ranks.")),
                    Paragraph(Text("For one direction write s=card(C.slice(1)) and t=card(C.slice(d-1)), and assume "
                        + "t<s+k+1. When s=0, t<=k. Let M be all labels whose complementary coatom is missing "
                        + "from C. Then card(M)=d-t>=d-k. Every member of C contains M: an omitted label of M "
                        + "would put that member below a missing coatom, contrary to upperness. The principal-filter "
                        + "bound contradicts C's strict mass hypothesis. When s=1, upperness supplies the d-1 "
                        + "coatoms containing the unique singleton, so t-s>=d-2>k, again impossible. When s>=2, "
                        + "each coatom contains a selected singleton and t=d. The small-gap assumption forces at "
                        + "least d-k singleton labels in C. Cross-intersection forces every member of D to contain "
                        + "all those labels, so D's principal-filter bound contradicts its strict mass hypothesis. "
                        + "Interchanging the families proves the second conjunct. Both upperness assumptions are "
                        + "used through these two directions; the partner's mass is essential.")),
                    Paragraph(Text("The endpoints k=0 and k=d-3 are included, in particular d=3,k=0. The earlier "
                        + "gap-two theorem is the k=1 consequence for d>=4 and retains its original statement. "
                        + "Strictness cannot be replaced by weak mass inequalities: for unit weights choose "
                        + "card(A)=d-k, C all supersets of A and D all sets meeting A. They are cross-intersecting "
                        + "upper families; C has mass H(d,k)=2^k, D has mass 2^d-2^k, and C has gap k. "
                        + "The range cannot extend to k=d-2: a one-point star on both sides has unit mass "
                        + "2^(d-1)>H(d,d-2)=2^(d-2), but gap d-2 rather than d-1. A large first-side mass "
                        + "alone likewise gives no such conclusion. This is a repository derivation; no literature "
                        + "priority, sharp polygon bound or attainment is asserted.")),
                    Paragraph(Text("Conditional ordinary application to n=24. Retain the original domain of B-33, "
                        + "B-37 and B-41 in the intrinsic-classification-and-polygon-geometry theory source: an "
                        + "arbitrary labelled strictly convex 24-gon; any six distinct pairwise compatible actual "
                        + "ears D={f_ab} labelled by E(K4), allowing shared endpoints; any four prescribed actual "
                        + "triangulations T_a with complete Ear(T_a)=S_a; and any family F containing these witnesses "
                        + "and intersecting on full actual ear sets. Gamma(H) contains every actual triangulation "
                        + "with exact D trace H, with every outside-D ear and every distinct completion retained. "
                        + "The following inference is conditional on the complete B-37/B-41 compression, counting, "
                        + "fullness and loss chains. This generic Lean theorem alone does not compile those chains "
                        + "or certify an end-to-end n24 maximum or classification. B-47 of the same-parity-deficit "
                        + "volume treats n=23; it does not already contain this n24 consequence.")),
                    Paragraph(Text("For each pair i!=j take P=M_i, Q=M_j, K=P union Q. The two original sides are "
                        + "F intersect X(P|Q) and F intersect X(Q|P); they contain their respective cores, are "
                        + "disjoint as actual triangulations, and their cardinalities sum to the original z_ij. "
                        + "All common ears lie in E_K, the full set of ears outside K compatible with each ear of K. "
                        + "It includes the third matching and compatible outside-D ears, and is not restricted to "
                        + "ears compatible with all six D ears. B-37.2's local delete/restore maps preserve the "
                        + "forced and forbidden sets separately on each side. Its maximal cross-pair replacement "
                        + "and projection preserve cross-intersection and do not decrease either mass. They yield "
                        + "a common compatible J subset E_K and upper cross-intersecting families C,D. Each pair "
                        + "may have a different J. Nonempty cross-intersection gives d=card(J)>=1, and compatibility "
                        + "of J union K gives d+4<=12, hence d<=8. No fixed K is required to attain eight, and no "
                        + "parity, symmetry, saturation, protection carrier or common compression carrier is imposed.")),
                    Paragraph(Text("Put c_r=Catalan(22-r), V_r=c_(r+2)-2*c_(r+3)+c_(r+4), and "
                        + "omega_r^(d)=sum(j=0,...,d-r) (-1)^j*binom(d-r,j)*V_(r+j). Forcing r selected J ears "
                        + "and P, excluding Q, then excluding the unselected observed J ears gives precisely these "
                        + "complete actual fiber counts. Unobserved ears stay free. Swapping the sides gives the "
                        + "same weights because card(P)=card(Q)=2. The largest c index is d+4<=12, leaving at "
                        + "least twelve vertices in each count. B-37/B-41's conditional flip injections give "
                        + "nonnegative decreasing weights and G_d=omega_0^(d)-omega_d^(d)>0, decreasing with d. "
                        + "With alpha_r=card(C.slice(r))/binom(d,r), upperness gives increasing alpha_r, and "
                        + "cross-intersection gives alpha_0=0, alpha_d=1 and disjointness of the complement image "
                        + "of C from D. Consequently the original deficit d_ij=s-z_ij is at least "
                        + "sum(0<=r<d/2) binom(d,r)*(omega_r^(d)-omega_(d-r)^(d))*(alpha_(d-r)-alpha_r). "
                        + "All terms are nonnegative; r=0 contributes G_d and r=1 contributes "
                        + "(omega_1^(d)-omega_(d-1)^(d))*(card(C.slice(d-1))-card(C.slice(1))).")),
                    Paragraph(Text("Here s=3507232740 and T=V_6=1396652. Exact integer evaluation gives "
                        + "H(6,0)=1396652, H(7,1)=1010990+385662=1396652, and "
                        + "H(8,2)=732564+2*278426+107236=1396652. If original core sizes a_i,a_j>T, "
                        + "each original side, hence each compressed mass, is greater than T. Apply the theorem "
                        + "at (d,k)=(6,0),(7,1),(8,2). The corresponding G_d values are "
                        + "539668320,396434720,291031620; the rank-one minus coatom weight differences are "
                        + "193270840,143233600,105403100. Thus d_ij is at least "
                        + "732939160,682901920,607240920 respectively. For d<=5 retain G_d>=G_5=732939160. "
                        + "Every active pair has the basic bound G_d>=G_8=291031620, and every pair with both "
                        + "cores above T has d_ij>=607240920. These omega differences are dimension-specific "
                        + "conditional weights, not the original six-ear trace weights w_r.")),
                    Paragraph(Text("All losses belong to the same original F. In B-37 notation set eta=u0-u, "
                        + "r_i=w4-b_i, ell_i=2*w3-t_i and d_ij=s-z_ij, where a_i,b_i,t_i,u,z_ij are the "
                        + "original exact-trace counts. The unchanged identities are "
                        + "card(F)-L=a_k-(eta+r_k+ell_i+ell_j+d_ij) and "
                        + "2*(card(F)-L)=h-2*eta-sum_i ell_i-sum_(i<j) d_ij, with "
                        + "L=12909891720 and h=w2-w4=1623971580. When all three cores are active, "
                        + "B-37.7 gives eta>=0,r_i>=1,ell_i>=2 from original fullness obstructions and complete-ear "
                        + "realizations, without A>W. If some a_k<=T, the first identity gives "
                        + "card(F)-L<=1396652-5-291031620=-289634973, hence card(F)<=12620256747. "
                        + "If all a_i>T, the second gives 2*(card(F)-L)<=1623971580-6-3*607240920=-197751186, "
                        + "hence card(F)<=12811016127=L-98875593<L. These exhaust the three-active-core case. "
                        + "The pair estimates all bound losses of this same F; their combination does not assert "
                        + "simultaneously attained marginal optima or simultaneous compressions.")),
                    Paragraph(Text("Conditionally consuming the remaining original B-33.3/B-37.3/B-37.5/B-37.9 "
                        + "chains, the original residual domain consists of allowed F with all a_i>0 and A>w2. "
                        + "Its finite maximum is below L when nonempty; its value is defined as zero when empty. "
                        + "Thus the ordinary inference gives K0=max(L,K_res)=L and transfers the existing twelve "
                        + "labelled full-fiber equality families, without a symmetry quotient. Explicitly, let "
                        + "U0={S1,S2,S3,S4} union (binom(D,4) minus {Q1,Q2,Q3}) union binom(D,5) union {D}. "
                        + "Choose i, order the other indices j<k, and independently for each x in M_i choose E_x "
                        + "from {M_j union {x}, M_k union (M_i minus {x})}. The trace family is "
                        + "B_(i,E)=U0 union {M_i,Q_j,Q_k} union {M_i union {z}:z in D minus M_i} union {E_x:x in M_i}; "
                        + "the actual family is the union of Gamma(H) over H in B_(i,E). The cited realization "
                        + "and full-fiber equality chains supply attainment, distinction and exhaustion for the "
                        + "arbitrary fixed four witnesses. This paragraph is conditional ordinary mathematics, "
                        + "not a kernel-verified polygon classification. No residual inhabitation, sharpness or "
                        + "attainment of the three-core bound, n>=25 conclusion, or completion of the larger FIB "
                        + "goal follows from this generic unit."))),
                DescribeRole.Theorem)), []));
}
