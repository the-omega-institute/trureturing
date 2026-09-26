using System;
using System.Collections.Generic;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CriticalTransitionStarDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/CriticalTransitionStar.critical_transition_star";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A six-occurrence critical edge has strict angle-sum margins on both continuous faces, allowing two transition occurrences.",
        H("Critical opposite floors and a mixed six-valent star"),
        Blocks(
            Paragraph(Text("I is an arbitrary finite type of cardinality six. "
                + "The five functions y,z,o,v,w:I -> Real retain every local occurrence. The target "
                + "coordinate is shared. At each occurrence the order is (12,13,14,34,24,23); "
                + "o is opposite the target and y,z,v,w are its four neighbours. All five "
                + "coordinates lie in [1,2]. ThreeSmall means at least three of the four "
                + "neighbours are at most 5/4, expressed as the four possible conjunctions.")),
            Paragraph(Text("good is a finite subset of I with at least four members. At every good "
                + "occurrence all four neighbours are at most 5/4 and o is at least 4/3. "
                + "No equality of the target and opposite, no prescribed angle and no angle-sum "
                + "inequality is a hypothesis. AngleSum(a,y,z,o,v,w) below abbreviates the sum "
                + "over i:I of arccos(cosine(a,y(i),z(i),o(i),v(i),w(i))). cosine is the "
                + "original six-variable expression from FourCycleEnvelopes, not a free function.")),
            Paragraph(Text("Define beta=arccos(49/sqrt(6534)), gamma=arccos(43/99), and "
                + "margin=min(2pi-6arccos(4/7),4gamma+2beta-2pi). These are exactly the "
                + "three definitions in the paired Lean source.")),
            Describe.Lean(
                DescribeId.Create("critical-transition-continuous-star"),
                DeclarationHandle.Create(Declaration),
                H("Both boundary sums have the same positive margin"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Reuse the derivative-based mixed comparison from the single "
                        + "analytic owner. The lower target 4/3 gives cosine at least 4/7. "
                        + "At target 2 the four possible three-small-neighbour endpoints each "
                        + "give squared cosine 2401/6534. Four small neighbours and opposite "
                        + "floor 4/3 give exactly 43/99. Denominator positivity and square-root "
                        + "comparison are proved within the source.")),
                    Paragraph(Text("For gamma in [0,pi/2], cos(2gamma)=-6103/9801. The positive "
                        + "square comparison (6103/9801)^2-2401/6534=3896615/192119202 proves "
                        + "2gamma>pi-beta. This gives 4gamma+2beta>2pi. The lower gap follows "
                        + "from 4/7>cos(pi/3). Summing beta plus the good-occurrence increment "
                        + "gamma-beta, and using card(good)>=4, gives the actual six-occurrence "
                        + "upper-face bound. It is not a theorem with the desired budget assumed.")),
                    Paragraph(Text("The quantified functions vary over continuous faces. Pullbacks "
                        + "of one shared global length vector are included among these functions; "
                        + "the source does not construct the global incidence carrier or prove "
                        + "manifold links, co-volume existence or the full CFMP conjecture. "
                        + "The ordinary application uses favourable opposites of the same degree "
                        + "class, so it is preserved by unbranched covers even when global "
                        + "edge identities split. The statement itself does not certify the "
                        + "cover construction or its geometric realization."))),
                DescribeRole.Theorem),
            Describe.Remark(
                DescribeId.Create("written-flat-pair-mean-obstruction"),
                H("Written continuation: flat pairs constrain shared lengths"),
                F.Disp(FlatPairMeanFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/cfmp2026criticaltransition")),
                Blocks(
                    Paragraph(Text("This authored Remark records written mathematics beyond "
                        + "critical_transition_star. It names no new Lean declaration and does "
                        + "not enlarge that theorem's kernel-certified statement. PositiveLengths "
                        + "denotes the six positive original edge lengths; OppositePairs consists "
                        + "of the three unordered pairs of opposite local edges. FlatAt(ell,q) "
                        + "means that the extended hyperideal angles are pi on q and zero on "
                        + "the other four edges. MeanCosh(ell,q) is cosh of the arithmetic "
                        + "mean of the two LENGTHS in q. OtherPairOne and OtherPairTwo denote "
                        + "the remaining two opposite pairs, in either order.")),
                    Paragraph(Text("Luo-Yang Corollary 4.12 supplies the C1 convex extended "
                        + "co-volume whose gradient is the extended angle vector. Subtracting "
                        + "the flat angle vector's linear functional makes its fixed-gradient "
                        + "fibre a convex minimizer set. The tetrahedral Klein four group "
                        + "preserves that flat angle vector. Its length average is "
                        + "(u,v,w,u,v,w). With X=cosh(u),Y=cosh(v),Z=cosh(w), the original "
                        + "cosine satisfies phi+1=(X+1)*((Y+Z)^2-(X-1)^2)/D, where "
                        + "D=X^2+Y^2+Z^2+2XYZ-1>0. This proves the displayed necessary "
                        + "inequality. The local average is not assumed to be an admissible "
                        + "global length modification. Equivalence is asserted only for "
                        + "opposite-pair-equal length vectors.")),
                    Paragraph(Text("Actual global edge-pair multisets must share the same "
                        + "MeanCosh value. A flat candidate points from its pi pair to its "
                        + "two zero pairs and forces strict decrease, so directed cycles "
                        + "are impossible. A pi pair AB with zero pairs AA and BB is also "
                        + "excluded by convexity of cosh. Consequently, with exactly two "
                        + "global edges, each occurring at least twice in every tetrahedron, "
                        + "mixed pi pairs are impossible. A pure pi pair saturates one "
                        + "global edge and contradicts any genuine tetrahedron. The strict "
                        + "angle construction and the cited maximizer theorem therefore give "
                        + "realization under minimum degree six in the strict boundary "
                        + "setting. The three-tetrahedron example has degrees six and twelve "
                        + "and one genus-two boundary.")),
                    Paragraph(Text("The same bound gives the sharp all-geometric interval "
                        + "criterion cosh(M)<1+2cosh(m) for 0<m<=M, and the genuine positive "
                        + "cosh cube (1,3]^6. It does not extend the old neighbour-monotonicity "
                        + "domain: an explicit genuine point has a negative neighbour "
                        + "derivative. General CFMP, arbitrary one/five local label patterns, "
                        + "and completeness of the flat-candidate elimination remain outside "
                        + "these conclusions. The source note credits the existing small-"
                        + "manifold census; this example is not asserted to be a new "
                        + "homeomorphism type. No compilation or projection receipt for "
                        + "this new Remark is claimed here.")))),
            Describe.Remark(
                DescribeId.Create("written-flat-support-low-edge-closure"),
                H("Written continuation: two global edges and two-flat support"),
                F.Disp(TwoEdgeWrittenFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/cfmp2026criticaltransition")),
                Blocks(
                    Paragraph(Text("This is an authored written-mathematics Remark, not a new "
                        + "Lean declaration or an extension of critical_transition_star. "
                        + "StrictBoundaryTriangulations means finite connected orientable "
                        + "actual face-paired ideal triangulations with every vertex link a "
                        + "closed surface of genus at least two. MinimumDegreeSix counts "
                        + "local edge occurrences. EdgeCount counts actual global edge "
                        + "equivalence classes. GenuineRealization means a nondegenerate "
                        + "hyperbolic metric on that same triangulation with totally geodesic "
                        + "boundary. No local two/four label quota is a premise below.")),
                    Paragraph(Text("For actual cosh coordinates (r,a,b,o,c,d)>1, the two "
                        + "cosine radicands are squared norms of the Cauchy vectors written "
                        + "in the source note. Their nonnegative remainder J gives the exact "
                        + "flat condition (r-1)(o-1)>=(sqrt(ac)+sqrt(bd))^2+J. Equality J=0 "
                        + "holds exactly at a=c,b=d. The necessary product gap "
                        + "sqrt(ro)>=1+sqrt(ac)+sqrt(bd) is distinct from the previous "
                        + "cosh-of-mean bound. It is not asserted to be sufficient.")),
                    Paragraph(Text("The existing strict-angle construction and the cited "
                        + "Luo-Yang maximizer theorem give common positive generalized "
                        + "lengths and at most EdgeCount-1 flat blocks. With two edges a "
                        + "remaining unique flat must have five A cosh coordinates and one "
                        + "B, with B>4A+5. Every other B-containing block has at least two "
                        + "B occurrences. The nine continuous local graph estimates make "
                        + "their total B angle exceed pi/4 per occurrence, contradicting "
                        + "the global 2pi sum. The (6,18) four-tetrahedron packet explicitly "
                        + "has singleton-label blocks outside the earlier local quota.")),
                    Paragraph(Text("There is a further result without restricting the total "
                        + "global edge count: if minimum degree is six, at least one block "
                        + "is genuine and at most two are flat, the pi slots use pairwise "
                        + "distinct global labels. A saturated label is confined to the flat "
                        + "blocks. Exact face signatures leave only single/five or star/star "
                        + "supports. Face connectivity excludes the first; matching the "
                        + "unique longest nonstar edge excludes the second by strict shared "
                        + "length order or a degree-two contradiction. Thus three global "
                        + "edges leave at most one flat block. If all actual label types "
                        + "occur at least twice, none can be flat.")),
                    Paragraph(Text("The four-tetrahedron witness is not a newly claimed "
                        + "census type. The positive arccosh(3) cube is already Feng-Ge-Hua "
                        + "Theorem 3.9. No new kernel, Scribe compilation, projection or "
                        + "independent review receipt is asserted. Full CFMP, an isolated "
                        + "flat using three independent lengths, and larger flat sets "
                        + "remain outside the displayed conclusions.")))),
            Describe.Remark(
                DescribeId.Create("written-colouring-flat-interface"),
                H("Written colouring continuation: states, parity and interfaces"),
                F.Disp(ColourMismatchFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/cfmp2026criticaltransition")),
                Blocks(
                    Paragraph(Text("This authored research Remark is separate from the original "
                        + "Lean declaration. StrictBoundaryTriangulations has the existing actual "
                        + "finite orientable face-pairing meaning. PositiveGeneralizedLengths "
                        + "means one positive original length per global edge; ZeroEdgeCurvature "
                        + "means every occurrence-counted angle sum is 2pi. SaturatedDegreeAtLeastThree "
                        + "requires degree at least three at every edge carrying two pi occurrences.")),
                    Paragraph(Text("A flat state is one of the three unordered 2+2 vertex partitions. "
                        + "The two within-class edges carry pi, the four cross-class edges zero. "
                        + "A flat tetrahedron marks one edge in each triangular face. "
                        + "MismatchedFlatFaceCount counts paired flat/flat faces once when their "
                        + "marked edge occurrences disagree under the actual face map. This "
                        + "does not assert a mismatch of the faces' intrinsic metrics.")),
                    Paragraph(Text("SaturatedEdgeCount counts actual global edges with two pi "
                        + "occurrences. Such an edge has no genuine occurrence and its binary "
                        + "normal cycle has at least two status changes. One mismatched face "
                        + "accounts for exactly two changed edge slots, with repeated labels "
                        + "counted as occurrences. Summing proves the displayed inequality "
                        + "without bounding the number of flat tetrahedra.")),
                    Paragraph(Text("Rainbow global three-edge colours require all edge degrees "
                        + "to be even. If degrees are constant within each colour and their "
                        + "reciprocals sum to less than one half, the classical hyperideal angle "
                        + "existence and uniqueness theorem constructs a genuine shared metric. "
                        + "For the triple six,six,eight, cosh-lengths are 2+3sqrt(2)/2, "
                        + "2+3sqrt(2)/2, 2+sqrt(2). A completely specified 48-tetrahedron "
                        + "group construction gives four genus-two boundary components.")),
                    Paragraph(Text("Taut and veering structures are credited combinatorial "
                        + "frameworks, not automatic hyperideal geometric realizations. The "
                        + "known nine-degree P4 example cannot have rainbow three-edge colours. "
                        + "No new formal theorem, compilation or projection receipt, complete "
                        + "CFMP proof, or mathematical-priority claim accompanies this Remark.")))),
            Describe.Remark(
                DescribeId.Create("written-exposed-pi-edge-budget"),
                H("Written continuation: every flat set exposes a pi edge"),
                F.Disp(ExposedPiEdgeFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/cfmp2026criticaltransition")),
                Blocks(
                    Paragraph(Text("This authored research Remark records ordinary written "
                        + "mathematics and names no new Lean declaration. T ranges over actual "
                        + "finite orientable face-paired ideal triangulations in the existing "
                        + "strict boundary setting. PositiveGeneralizedLengths assigns one "
                        + "positive original length to every actual global edge. "
                        + "ZeroEdgeCurvature requires the occurrence-counted sum at each "
                        + "global edge to be 2pi. MinimumDegreeSix counts occurrences.")),
                    Paragraph(Text("FlatSet is the entire set of flat tetrahedra under this "
                        + "same generalized length vector. For each global edge e, m(e) "
                        + "counts its pi slots in FlatSet and n(e) counts all its flat slots. "
                        + "ExposedPiEdges consists of those with m(e)=1 and n(e) equal to one "
                        + "or two. HasFlat means FlatSet is nonempty. The displayed conclusion "
                        + "asserts this exact exposed set is nonempty, with no bound of two "
                        + "on the number of flat tetrahedra and no colouring premise.")),
                    Paragraph(Text("The existing Cauchy remainder and AM-GM give, for flat "
                        + "cosh coordinates (r,a,b,o,c,d) with selected pair r,o, "
                        + "2log(r)+2log(o)-log(a)-log(b)-log(c)-log(d)>log(16). "
                        + "Summing uses the shared value w(e)=log(cosh(ell(e)))>0 and "
                        + "coefficient 3m(e)-n(e). At m=2 saturation forces n=degree>=6; "
                        + "at m=0 the coefficient is nonpositive. Only the exposed edges "
                        + "can provide the necessary positive sum. Their cosh products "
                        + "satisfy product x(e)^(3-n(e))>16^card(FlatSet), hence "
                        + "product x(e)>4^card(FlatSet). The complete positive correction "
                        + "terms are retained in the written theory.")),
                    Paragraph(Text("Every exposed edge has at least four genuine local "
                        + "occurrences, with angle sum exactly pi and at least one angle "
                        + "at most pi/4. These occurrences need not be distinct tetrahedra. "
                        + "The pi-selection multigraph has one edge per flat tetrahedron "
                        + "and graph degree m(e)<=2. Its path count p obeys v_pi=f+p. "
                        + "Each flat-only face component requires a different path "
                        + "component by the same signed budget and saturated normal "
                        + "circle argument, so f<=v_pi-c_F. Cycle components can remain.")),
                    Paragraph(Text("Luo-Yang Lemma 4.3 defines each positive face-corner "
                        + "truncation length from the shared original face lengths. "
                        + "A flat corner's longest side is at least the sum of the two "
                        + "others. Following longest sides through mismatched flat faces "
                        + "strictly increases this shared length. A closed all-mismatch "
                        + "corner walk is impossible; genuine blocks and compatible flat "
                        + "faces are allowed terminal states. The two local cosh vectors "
                        + "(2,2,2,20,2,2) and (2,2,2,2,20,2), sharing face123, exhibit "
                        + "a legal local mismatch. They are not a complete CFMP instance.")),
                    Paragraph(Text("These are necessary conditions, not a proof that the "
                        + "small genuine angles or large exposed lengths cannot occur. "
                        + "The original critical_transition_star statement and Lean source "
                        + "are unchanged. No Scribe compilation or projection, new kernel "
                        + "certification, independent referee approval, full CFMP proof "
                        + "or counterexample is represented by this Remark.")))),
            Describe.Remark(
                DescribeId.Create("written-endpoint-caps-anisotropic-matching"),
                H("Written continuation: endpoint caps and unequal transverse pairs"),
                F.Disp(EndpointCapFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/cfmp2026mixedmatching")),
                Blocks(
                    Paragraph(Text("This authored Remark describes ordinary written mathematics, "
                        + "not a new Lean declaration. GenuineHyperidealAngles is the six positive "
                        + "dihedral angles with each vertex sum below pi. TetrahedronEdges is "
                        + "the six local edges. EndpointSumsAtMostHalfPi(a,e) requires the sums "
                        + "of the three angles at EACH endpoint of e to be at most pi/2. "
                        + "CoshOriginalEdgeLength(a,e) is the actual angle-to-length formula, "
                        + "whose denominator reads endpoint vertex triples, not face triples. "
                        + "No equality between angles or lengths is assumed.")),
                    Paragraph(Text("More generally, endpoint caps sigma1,sigma2<=pi/2 imply "
                        + "ell(e)<asinh(tan(sigma1/2))+asinh(tan(sigma2/2)). Cauchy-Schwarz "
                        + "in the positive matrix [[1,cos(theta)],[cos(theta),1]], followed by "
                        + "D=(cos(theta)+cos(a+b))*(cos(theta)+cos(a-b)), proves the bound. "
                        + "At equal cap sigma the sharp cosh supremum is "
                        + "(3-cos(sigma))/(1+cos(sigma)). The genuine angle family "
                        + "(sigma-2eps,eps,eps,eps,eps,eps) approaches it. Frigerio-Moraschini "
                        + "Section 1.1 and Luo-Yang Section 6.1 supply the classical inverse "
                        + "formula; they are not claimed as new results.")),
                    Paragraph(Text("A separate window with target and three adjacent angles "
                        + "at most pi/5 and the fourth at most pi/3 gives cosh(ell) "
                        + "<sqrt(237620/28431)<3. The endpoint determinant bounds are "
                        + "243/125 and 117/100, and the numerator is less than 109/25. "
                        + "Either bound can certify genuine occurrences of the two pi labels "
                        + "of a proposed flat. Shared lengths below three then contradict "
                        + "the existing flat requirement (r-1)*(o-1)>4. Such qualifying "
                        + "witnesses are not automatically supplied by minimum degree.")),
                    Paragraph(Text("The actual four-class patterns C=(R,A,B,R,A,B) and "
                        + "D=(R,A,B,S,A,B) have per-edge occurrence counts R:(p,q), "
                        + "A:(u,v), B:(h,k), S:(0,w), all parameters positive and degrees "
                        + "at least six. Counts imply pv=2qu and pk=2qh. Merging R,S "
                        + "gives a rainbow colouring, so actual oriented endpoint return "
                        + "forces even degrees. Typewise angle averaging preserves each "
                        + "edge equation; Luo-Yang and genuine D rigidity yield common "
                        + "R,A,B,S lengths without requiring A=B.")),
                    Paragraph(Text("All three flat C states are excluded. Flat R forces "
                        + "p=1,q>=5,u and h even, so a genuine R occurrence has both "
                        + "endpoint sums at most 2pi/5 and R<3. Flatness requires "
                        + "R>=1+A+B>3. Flat A forces u=1,v odd,p divisible by four. "
                        + "The exact cosine difference gives sign(beta-delta)=sign(A-B), "
                        + "putting A in the four-small/one-medium window and contradicting "
                        + "A>3. The B branch interchanges the transverse classes.")),
                    Paragraph(Text("The complete 22-tetrahedron packet has edge degrees "
                        + "6,6,6,6,20,22,22,44, one genus-fifteen vertex link and counts "
                        + "(p,q,u,v,h,k,w)=(1,5,2,20,4,40,20). Its even face permutations "
                        + "are compatible with a specified alternating tetrahedron "
                        + "orientation. All sixteen link-vertex fans and oriented first "
                        + "returns are checked. The angle equations force A>B; connected "
                        + "cyclic covers yield an unbounded genuinely anisotropic family. "
                        + "The local caps need no role balance, but this global realization "
                        + "theorem still does. Full CFMP, new Lean certification, Scribe "
                        + "compilation or projection, CI, Freeze and independent review "
                        + "approval are not asserted.")))),
            Describe.Remark(
                DescribeId.Create("written-coupled-budget-singleton-realization"),
                H("Written continuation: coupled endpoint budgets without role averaging"),
                F.Disp(SingletonRealizationFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/cfmp2026mixedmatching")),
                Blocks(
                    Paragraph(Text("This is authored written mathematics, not a new Lean "
                        + "declaration. StrictBoundaryTriangulations means actual finite "
                        + "connected orientable face-paired ideal triangulations with every "
                        + "vertex link a closed surface of genus at least two. "
                        + "ThreeEdgesTwoSingletonLabels means the actual global edge set "
                        + "is exactly three distinct labels U,V,H, with U and V each "
                        + "occurring at most once in every tetrahedron. They may be absent. "
                        + "MinimumDegreeSix counts all actual local occurrences. "
                        + "GenuineRealization concerns the same prescribed triangulation. "
                        + "No role balance, equal angles, local templates or automorphism "
                        + "hypothesis is part of the displayed assertion.")),
                    Paragraph(Text("For genuine angles (theta,a,b,g,c,d), put u=a+b,v=c+d. "
                        + "The exact half-angle form of the classical inverse formula proves "
                        + "cosh(ell12)<1+2sin(theta)^2/((cos(theta)+cos(u))*(cos(theta)+cos(v))). "
                        + "Both endpoints retain the same theta. For caps sigma1,sigma2<pi, "
                        + "m=min(sigma1,sigma2), M=max(sigma1,sigma2), the sharp supremum "
                        + "is 1+2(1-cos(m))/(cos(m)+cos(M-m)). A genuine small-epsilon "
                        + "family attains it in the limit. Frigerio-Moraschini supplies "
                        + "the inverse formula, not this claimed research derivation.")),
                    Paragraph(Text("Logarithmic concavity gives a particularly useful "
                        + "consequence: the SUM of the two endpoint vertex-angle sums "
                        + "at most pi implies cosh(ell)<3. One endpoint may exceed pi/2. "
                        + "Every genuine occurrence of a common edge with cosh length "
                        + "at least three therefore needs 2*target_angle plus its four "
                        + "adjacent angles to exceed pi. Summing preserves actual "
                        + "neighbour multiplicities; they are not generally one. The "
                        + "separate individual-angle window allows the fourth neighbour "
                        + "to reach 7pi/15 when target and three neighbours are at most pi/5.")),
                    Paragraph(Text("The strict-angle construction and Luo-Yang Theorems "
                        + "1.4 and 6.3 give common positive generalized lengths. With "
                        + "three edges there are at most two flat blocks. Singleton "
                        + "U,V cannot saturate, and H occurs in every genuine block, "
                        + "so no label saturates and at most one flat remains. A selected "
                        + "singleton pi label then has at least five genuine occurrences. "
                        + "If its cosh length were at least three, they would demand "
                        + "more than 5pi; all actual available angles give at most "
                        + "2pi+3pi. Thus the selected singleton cosh length is below three. "
                        + "Both possible types of pi pairs contradict the existing flat "
                        + "Cauchy product bound, proving the displayed realization.")),
                    Paragraph(Text("Changing just (1,0;3,0;0132) to (1,0;3,0;0213) in "
                        + "the earlier eleven-block face table yields actual degrees "
                        + "6,6,54 and one genus-nine vertex link. All three oriented "
                        + "first-return cycles and six link fans are checked. The unique "
                        + "(U,H,H,V,H,H) block prevents applying the earlier repeated-type "
                        + "criterion. Cyclic covers use metric lifting; their 3n edges "
                        + "do not satisfy the three-edge hypothesis when n>1.")),
                    Paragraph(Text("DNA tetrahedron experiments motivate compatible paired "
                        + "data; they are not geometric proof inputs. Ge's 2026-09-23 "
                        + "preprint asserts existence of some geometric triangulation, "
                        + "which is distinct from realizing this prescribed triangulation. "
                        + "New numerical and finite checks supplement the written "
                        + "arguments. Full CFMP, independent review, new Lean certification, "
                        + "Scribe compilation/projection, CI and Freeze are not claimed.")))))));

    private static Formula SingletonRealizationFormula()
    {
        var t=F.Id("T");
        return All([("T",F.Id("StrictBoundaryTriangulations"))],
            Imp(And(Call("MinimumDegreeSix",t),
                    Call("ThreeEdgesTwoSingletonLabels",t)),
                Call("GenuineRealization",t)));
    }

    private static Formula EndpointCapFormula()
    {
        var a=F.Id("a"); var e=F.Id("e");
        return All([("a",F.Id("GenuineHyperidealAngles")),
                    ("e",F.Id("TetrahedronEdges"))],
            Imp(Call("EndpointSumsAtMostHalfPi",a,e),
                Lt(Call("CoshOriginalEdgeLength",a,e),F.D(3))));
    }

    private static Formula ExposedPiEdgeFormula()
    {
        var t=F.Id("T"); var ell=F.Id("ell");
        return All([("T",F.Id("StrictBoundaryTriangulations")),
                    ("ell",Call("GlobalLengthVectors",t))],
            Imp(And(Call("PositiveGeneralizedLengths",t,ell),
                    Call("ZeroEdgeCurvature",t,ell),
                    Call("MinimumDegreeSix",t),Call("HasFlat",t,ell)),
                Call("Nonempty",Call("ExposedPiEdges",t,ell))));
    }

    private static Formula ColourMismatchFormula()
    {
        var t=F.Id("T"); var ell=F.Id("ell");
        return All([("T",F.Id("StrictBoundaryTriangulations")),
                    ("ell",Call("GlobalLengthVectors",t))],
            Imp(And(Call("PositiveGeneralizedLengths",t,ell),
                    Call("ZeroEdgeCurvature",t,ell),
                    Call("SaturatedDegreeAtLeastThree",t,ell)),
                Le(Call("SaturatedEdgeCount",t,ell),
                   Call("MismatchedFlatFaceCount",t,ell))));
    }

    private static Formula TwoEdgeWrittenFormula()
    {
        var t=F.Id("T");
        return All([("T",F.Id("StrictBoundaryTriangulations"))],
            Imp(And(Call("MinimumDegreeSix",t),Le(Call("EdgeCount",t),F.D(2))),
                Call("GenuineRealization",t)));
    }

    private static Formula FlatPairMeanFormula()
    {
        var ell=F.Id("ell"); var q=F.Id("q");
        var selected=Call("MeanCosh",ell,q);
        var one=Call("MeanCosh",ell,Call("OtherPairOne",q));
        var two=Call("MeanCosh",ell,Call("OtherPairTwo",q));
        return All([("ell",F.Id("PositiveLengths")),("q",F.Id("OppositePairs"))],
            Imp(Call("FlatAt",ell,q),
                Le(Call("add",F.D(1),Call("add",one,two)),selected)));
    }

    private static Formula Statement()
    {
        var i=F.Id("i"); var I=F.Id("I"); var g=F.Id("good");
        string[] names=["y","z","o","v","w"];
        var fs=names.Select(name=>F.Id(name)).ToArray();
        var values=fs.Select(f=>Apply(f,i)).ToArray();
        var box=All([("i",I)],And([..values.Select(x=>In(x,F.D(1),F.D(2)))]));
        var small=All([("i",I)],Call("ThreeSmall",values[0],values[1],values[3],values[4]));
        var paired=All([("i",I)],Imp(Member(i,g),And(
            Le(values[0],Rat(5,4)),Le(values[1],Rat(5,4)),
            Le(values[3],Rat(5,4)),Le(values[4],Rat(5,4)),Le(Rat(4,3),values[2]))));
        var premises=And(Call("Fintype",I),
            Eq(Apply(Qualified("Fintype","card"),I),F.D(6)),
            Le(F.D(4),Apply(Qualified("Finset","card"),g)),box,small,paired);
        var m=F.Id("margin"); var twoPi=Call("mul",F.D(2),F.Id("pi"));
        var lower=Call("AngleSum",[Rat(4,3),..fs]);
        var upper=Call("AngleSum",[F.D(2),..fs]);
        var result=And(Lt(F.D(0),m),Le(lower,Call("sub",twoPi,m)),Le(Call("add",twoPi,m),upper));
        var variables=new List<(string Name,Formula Type)>{("I",F.Id("Type"))};
        variables.AddRange(names.Select(name=>(name,
            (Formula)new Formula.TypeArrow(I,F.Id("Real")))));
        variables.Add(("good",Call("Finset",I)));
        return All([..variables],Imp(premises,result));
    }

    private static Formula All((string Name,Formula Type)[] vs,Formula body)=>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [..vs.Select(v=>new Formula.BoundVariable(FormulaIdentifier.Create(v.Name),v.Type))],body);
    private static Formula And(params Formula[] p)
    {
        if(p.Length==0) throw new ArgumentException("Empty conjunction");
        var r=p[^1]; for(var j=p.Length-2;j>=0;j--) r=new Formula.Logic(p[j],FormulaLogicOperator.And,r);
        return r;
    }
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Member(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula In(Formula x,Formula a,Formula b)=>Member(x,Call("Icc",a,b));
    private static Formula Apply(Formula function,params Formula[] args)=>
        new Formula.Apply(function,[..args]);
    private static Formula Qualified(string owner,string member)=>
        F.Seq(F.Id(owner),F.Dot,F.Id(member));
    private static Formula Rat(int n,int d)=>F.Seq(F.Frac,F.Grp(Number(n)),F.Grp(Number(d)));
    private static Formula Number(int value) => value switch
    {
        3 => F.D(3), 4 => F.D(4), 5 => F.D(5),
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };
    private static Formula Call(string name,params Formula[] args)
        => Apply(F.Id(name),args);
}