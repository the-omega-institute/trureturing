using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class TruncatedTetrahedronRelativeCWDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Gluing/TruncatedTetrahedronRelativeCW.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original finite raw tetrahedron quotients have actual characteristic maps and finite relative and absolute CW structures.",
        H("Relative and absolute cells of paired truncated tetrahedra"),
        Blocks(
            Describe.Lean(DescribeId.Create("upper-geometry"),
                DeclarationHandle.Create(Prefix + "upper_geometry"),
                H("Characteristic maps, ambient fibers and sphere attachment"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let T be any finite type with a chosen topology and a DiscreteTopology instance, and let P be a RawFacePairing T. The input consists of a fixed-point-free involution P.facePair on T times Fin 4 and mutually inverse permutations P.faceMap of the three edge slots. The type T may be empty. No topology or cell structure on the quotient is supplied as a hypothesis.")),
                    Paragraph(Text("Use the existing ActualLinkAffineFan.TruncatedPoint T, the product of T with the closed retained tetrahedron whose four coordinates lie between zero and 3/4 and sum to one. Its topology is the original product and subtype topology. RawFaceLinkPathConnected.frame and sigma extend the actual three-slot face permutation to four coordinates. The map truncatedMove P f transports the tetrahedron tag by P.facePair and reindexes all coordinates by the inverse sigma. TruncatedStep P a b holds precisely when a has zero f-th coordinate and b is that transported point for some f. Write X for this original retained carrier, R for the full equivalence closure of TruncatedStep, Q for TruncatedQuotient P with its quotient topology, and q for its canonical projection.")),
                    Paragraph(Text("Interior a means that every coordinate is nonzero. FaceInterior a f means that f is its unique zero coordinate. The first two clauses of UpperGeometry state the full ambient fibers: for every a,b in X with Interior a, q(a)=q(b) if and only if b=a; for every a,b,f with FaceInterior a f, truncatedMove P f a differs from a and q(a)=q(b) if and only if b=a or b=truncatedMove P f a. The quantified point b ranges over the entire original retained carrier. In particular, the cap interiors have singleton ambient fibers and a zero-face interior has exactly its two original paired representatives, even when the two faces belong to the same tetrahedron.")),
                    Paragraph(Text("Disk d is the closed unit ball in Fin d -> R with its subtype topology; Ball d and Sphere d denote the corresponding open unit ball and unit sphere. Three affine models retain respectively three or two coordinates and recover the last coordinate as mass minus their sum. All retained coordinates lie in [0,3/4]. The bulk model has mass one in dimension three; the zero-face model has mass one in dimension two; the cap model has mass 1/4 in dimension two and fixes its remaining original coordinate to 3/4. Their interiors are exactly the strict coordinate inequalities. They are compact convex sets with nonempty interiors. Mathlib's convex-body homeomorphism sends each model, interior and frontier to the closed ball, open ball and sphere.")),
                    Paragraph(Text("bulkDiskPoint t reconstructs all four original coordinates from the bulk disk. faceDiskPoint k t j reconstructs the complete original closed face, where k is hex or cap and the fixed j-th coordinate is respectively zero or 3/4. topCharacteristic P t and faceCharacteristic P k t j are q composed with these reconstructions. topCell and directedFaceCell extend these maps to PartialEquivs on the surrounding real coordinate spaces. The characteristic clauses assert continuity on Disk d, equality with these actual q-composites on every disk point, and singleton fibers within a fixed disk whenever the fiber meets its open ball. The chart clauses assert source Ball d, continuity on the closed ball, and continuity of the inverse on the open target. No closed characteristic map is asserted to be injective.")),
                    Paragraph(Text("PairedFace P is the quotient of directed tags (t,j) by y=x or y=P.facePair x. Its representative faceRep is chosen from that actual orbit. Involutivity proves coverage of all directed tags and separation of representative orbits; freeness rules out a singleton paired-face fiber. SurfaceCell P is (T times Fin 4) plus PairedFace P: its left summand consists of every original cap, and its right summand consists of one original zero face per actual pairing orbit. The maps surfaceCell select the corresponding directedFaceCell. These types are finite without a supplied cell count or a face table.")),
                    Paragraph(Text("The closed image clauses say topCell P t(ClosedBall 3)=q({a in X : a.tag=t}) and directedFaceCell P k t j(ClosedBall 2)=q(faceCarrier k t j), where faceCarrier fixes the tag t and coordinate j to zero or 3/4 according to k. Distinct top-cell open images are disjoint, and distinct surface-cell open images are disjoint. All top closed images together cover Q. These statements concern the actual quotient images, including every boundary identification.")),
                    Paragraph(Text("faceSkeleton P, abbreviated D, is the union of the closed surface-cell images. It equals q(retainedBoundary), where retainedBoundary consists of every a in X having some coordinate equal to zero or 3/4. The equality is proved in both directions using full closed-face reconstruction and actual pairing-orbit coverage. D is closed as a finite union of compact images in the Hausdorff quotient. Each top-cell open image is disjoint from D.")),
                    Paragraph(Text("Every top-cell sphere maps into D. The gauge sends the sphere back to the bulk frontier. A point of that frontier must have a boundary coordinate, since otherwise every retained inequality would be strict and the point would lie in the interior. A cap coordinate gives an original cap face. A zero coordinate gives an original paired face, transported to the selected representative when needed. This proves the genuine sphere-attaching condition for each three-cell.")),
                    Paragraph(Text("HigherCell n is the subtype of original tags t satisfying n=3. higherMap is topCell after that dimension equality. relativeCW P is Mathlib.RelCWComplex.mkFinite on all of Q relative to D, using the constructed open charts, their pairwise disjointness, their disjointness from D, the sphere-attaching condition, closedness of D and the closed cover. The final clause of UpperGeometry is RelCWComplex.Finite for this exact relativeCW instance. Its cells are empty in every dimension other than three and are indexed by T in dimension three. No CW structure on D is used.")),
                    Paragraph(Text("For the inverse-continuity step, a continuous map from a compact space to a Hausdorff space restricts to an embedding on an open subset when every full fiber meeting that subset is a singleton. The proof separates an open subset from its closed complement under the closed ambient map. Thus arbitrary identifications outside the open subset, including identifications inside a closed-cell boundary, remain allowed. Closedness of the original equivalence relation comes directly from FiniteZeroGuardedClosure.uniform_transport_and_closed_relation applied to these coordinate permutations. Compactness of the original retained carrier and normal separation then give Hausdorffness of the original quotient.")),
                    Paragraph(Text("The displayed formula expands all sixteen UpperGeometry clauses, including every characteristic-map and chart quantifier. Types denotes the chosen universe of types. The anonymous instance brackets denote a finite enumeration, a topology and a matching discrete-topology dictionary on T, in the same order as the Lean telescope. Disk d is the closed-ball subtype, val removes one subtype layer, source and target are the PartialEquiv sets, and inverse is its inverse map. ContinuousOn uses the inherited ambient topology. The function image(e,S) is the image of S under e, qTagCarrier(P,t) is exactly q P applied to {a : TruncatedPoint T | a.tag=t}, topUnion(P) is exactly the union over every t in T of image(topCell P t,ClosedBall 3), univ(Q) is the entire quotient, and finiteRelative(P) is precisely letI := relativeCW P; RelCWComplex.Finite (univ : Set (TruncatedQuotient P)) with base faceSkeleton P. The projection argument of UpperGeometry explicitly records which ambient observations the maps realize; the theorem supplies the original q.")),
                    Paragraph(Text("The theorem TruncatedTetrahedronCellGeometry.cell_geometry supplies complete ambient fiber laws and homeomorphisms onto every original closed bulk and face carrier. The retained-quotient definitions use the namespace TruncatedTetrahedronRelativeCW. The upper fiber fields follow from these fiber laws, and the closed-image equalities follow from the reconstruction homeomorphisms onto the entire closed carriers.")),
                    Paragraph(Text("For the original Section 17 pairing, take T=Fin 6 and P=actualPairing, with its existing finite discrete topology. An original row r maps to the orbit class of rowSource r; the original rows' coverage and separation give a bijection with PairedFace P. The chosen faceRep may be either side of that row. The same truncatedMove identifies their entire closed quotient images. The cap indices remain the original (t,j), and the top indices remain t. This identifies the constructed closed skeleton and relative cell geometry with the original quotient construction. The existing lower-dimensional assembly is combined with these original upper maps in the absolute finite CW application below."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Absolute finite CW application on the original quotient"), Blocks(
            Paragraph(Text("Let Q be the original TruncatedQuotient P, with its existing quotient topology and projection q P, and let C be all of Q. For every finite discrete type T and every RawFacePairing T, the lower cells of TruncatedTetrahedronLowerCW.lower_geometry combine with the upper characteristic maps above to give a finite absolute CW complex on C. The construction applies to the entire original quotient, including its boundary identifications, with no additional attachment or disjointness hypotheses.")),
            Paragraph(Text("Write L for the TruncatedTetrahedronLowerCW namespace and U for TruncatedTetrahedronRelativeCW. In dimension n use A(n) = L.LowerCell P n plus ({c : U.SurfaceCell P | n=2} plus U.HigherCell n). The characteristic PartialEquiv F(n,i) is L.lowerMap P n on the first summand, U.surfaceCell P c on the second after eliminating n=2, and U.higherMap P n on the third. The last map is U.topCell P t after eliminating n=3. Thus the zero-cells are the original old-vertex and midpoint classes, the one-cells are the supplied midpoint halfedges and cap edges, the two-cells are every cap and one zero face per pairing orbit, and the three-cells are indexed by the original tags T.")),
            Paragraph(Text("Every A(n) is finite: expand LowerCell and HigherCell and use the existing finite occurrence, quotient, subtype and sum instances. For n at least four, lower_geometry.no_higher_cells excludes the lower summand, and the other two summands have contradictory dimension tags. This proves the eventual-emptiness input to CWComplex.mkFinite. The source of every F(n,i) is the open unit ball. Continuity on the closed ball and continuity of the inverse on its target follow from lower_geometry.source_ball, characteristic_continuous and inverse_continuous in the lower branch, and upper_geometry.face_charts and top_charts in the other branches.")),
            Paragraph(Text("Let E be L.edgeSkeleton P and D be U.faceSkeleton P. The existing lower_union equality identifies E with the union of all lower closed-cell images, and lower_geometry.no_higher_cells restricts every such witness to dimension below two. Every lower open image is contained in E. The equality lower_geometry.original_locus identifies E with q P applied to originalEdges: points with two distinct zero coordinates, or with a coordinate equal to 3/4 and a different zero coordinate. Each such point has a boundary coordinate, so upper_geometry.skeleton_image gives E contained in D. Every surface open image also lies in D, by inclusion in its own closed image.")),
            Paragraph(Text("For open-cell disjointness, split both indices into their lower, surface and top summands and eliminate each dimension tag. Lower/lower pairs use lower_geometry.open_disjoint, surface/surface pairs use upper_geometry.face_open_disjoint, and top/top pairs use upper_geometry.top_open_disjoint. In each equal-dimensional branch, inequality of the full indices gives inequality of the corresponding original cell indices. The top/surface and top/lower pairs, in both orders, follow from upper_geometry.top_disjoint_skeleton and the inclusions into D just established.")),
            Paragraph(Text("For a surface/lower pair, represent the surface point by a = faceDiskPoint k t j x with x in the open disk. A lower point in the same quotient fiber has a representative b in originalEdges by lower_geometry.original_locus. The public faceBall_symm_interior_iff and faceRealize_strict_iff criteria in the TruncatedTetrahedronRelativeCW namespace give 0 < a_i < 3/4 for every i different from j; the original face reconstruction fixes a_j. On a cap, a_j=3/4, so every coordinate of a is nonzero. The full ambient interior_fibers law gives b=a, contradicting the zero coordinate present in either branch of originalEdges.")),
            Paragraph(Text("On a zero face, a_j=0 and every other coordinate is strictly positive and below 3/4. Thus FaceInterior a j holds, and the full ambient face_fibers law leaves exactly b=a or b=truncatedMove P j a. In the first alternative, two distinct zeros contradict uniqueness of j, and a 3/4 coordinate contradicts either a_j=0 or the strict upper bound away from j. In the moved alternative, the inverse sigma permutation pulls any two distinct zeros back to two distinct zeros of a; it also pulls any 3/4 coordinate back to a, where no such coordinate exists. Both alternatives exclude originalEdges. This proves surface/lower open disjointness through the full original equivalence closure, rather than through a restricted face relation.")),
            Paragraph(Text("For attachment of a surface sphere, a sphere point is outside the open disk. Composing the same two strict-interior criteria therefore supplies an index i different from the fixed face index j for which a_i is not strictly between zero and 3/4. The original closed-carrier bounds force a_i=0 or a_i=3/4. On a zero face, a_j=0, so these cases give respectively two distinct zeros or a cap coordinate together with a zero. On a cap face, a_j=3/4; the alternative a_i=3/4 is impossible because the two nonnegative coordinates already sum to 3/2 while all four sum to one. The remaining case is a_i=0. Hence every surface sphere maps into q P applied to originalEdges, which is E. The lower closed-union equality supplies an actual closed-cell witness of dimension below two, and its inclusion into the lower summand of A proves the precise sphere-attaching obligation.")),
            Paragraph(Text("The existing lower_mapsTo result supplies every lower sphere attachment, with each lower target index included into A. For a top sphere, upper_geometry.sphere_attaching places its image in D; expanding the union defining D supplies a surface closed-cell witness, now included in A(2). Finally, upper_geometry.top_closed_cover supplies a dimension-three closed-cell witness for every point of Q. Including these witnesses in A(3) proves that the union of all closed F-images is exactly C, not merely a selected component or a relative complement.")),
            Paragraph(Text("Apply CWComplex.mkFinite to C, A and F with these eventual-emptiness, finiteness, source, continuity, inverse-continuity, pairwise-disjointness, sphere-attachment and closed-cover proofs. Apply CWComplex.finite_mkFinite to the same data and the same obligations to obtain finiteness of that exact CW instance. Its own cell type in dimension n is A(n), so it has no cells in dimensions n at least four. No maximum dimension exactly three is asserted when T is empty: in that case the original carrier, quotient and all cell families are empty and the cover is vacuous. For nonempty T the construction uses the original three-cell maps. The lower midpoint subdivision handles retained-edge inversions, including self-identifications allowed by the raw pairing, without requiring edge freeness or changing the original quotient topology.")))))));

    private static Formula Statement()
    {
        var t = F.Id("T");
        return All("T", F.Id("Types"),
            F.Seq(F.OpenBracket, Call("Fintype", t), F.CloseBracket, F.Sp,
                F.OpenBracket, Call("TopologicalSpace", t), F.CloseBracket, F.Sp,
                F.OpenBracket, Call("DiscreteTopology", t), F.CloseBracket, F.Sp,
                All("P", Call("RawFacePairing", t), Conclusions())));
    }

    private static Formula Conclusions()
    {
        var p = F.Id("P"); var t = F.Id("T");
        var x = Call("TruncatedPoint", t); var q = Call("q", p);
        var d = Call("faceSkeleton", p);
        var a = F.Id("a"); var b = F.Id("b"); var f = F.Id("f");
        var tag = F.Id("t"); var other = F.Id("s"); var c = F.Id("c"); var e = F.Id("e");
        var top = Call("topCell", p, tag); var topOther = Call("topCell", p, other);
        var surface = Call("surfaceCell", p, c); var surfaceOther = Call("surfaceCell", p, e);
        var move = Call("truncatedMove", p, f, a);
        return And(
            All("a", x, All("b", x, Implies(Call("Interior", a),
                Iff(Eq(Apply(q,a), Apply(q,b)), Eq(b,a))))),
            All("a", x, All("b", x, All("f", Call("Fin",F.D(4)),
                Implies(Call("FaceInterior",a,f), And(Ne(move,a),
                    Iff(Eq(Apply(q,a),Apply(q,b)), Or(Eq(b,a),Eq(b,move)))))))),
            All("t",t,Characteristic(Call("topCharacteristic",p,tag),top,
                Call("bulkDiskPoint",tag),q,3)),
            All("k",F.Id("FaceShape"),All("t",t,All("j",Call("Fin",F.D(4)),
                Characteristic(Call("faceCharacteristic",p,F.Id("k"),tag,F.Id("j")),
                    Call("directedFaceCell",p,F.Id("k"),tag,F.Id("j")),
                    Call("faceDiskPoint",F.Id("k"),tag,F.Id("j")),q,2)))),
            All("t",t,Chart(top,3)),
            All("c",Call("SurfaceCell",p),Chart(surface,2)),
            All("t",t,Eq(Image(top,ClosedBall(3)),Call("qTagCarrier",p,tag))),
            All("k",F.Id("FaceShape"),All("t",t,All("j",Call("Fin",F.D(4)),
                Eq(Image(Call("directedFaceCell",p,F.Id("k"),tag,F.Id("j")),ClosedBall(2)),
                    Image(q,Call("faceCarrier",F.Id("k"),tag,F.Id("j"))))))),
            All("t",t,All("s",t,Implies(Ne(tag,other),
                Call("Disjoint",Image(top,Ball(3)),Image(topOther,Ball(3)))))),
            All("c",Call("SurfaceCell",p),All("e",Call("SurfaceCell",p),Implies(Ne(c,e),
                Call("Disjoint",Image(surface,Ball(2)),Image(surfaceOther,Ball(2)))))),
            Eq(Call("topUnion",p),Call("univ",Call("TruncatedQuotient",p))),
            Eq(d,Image(q,Call("retainedBoundary",t))),
            Call("IsClosed",d),
            All("t",t,Call("Disjoint",Image(top,Ball(3)),d)),
            All("t",t,Call("MapsTo",top,Call("Sphere",F.D(3)),d)),
            Call("finiteRelative",p));
    }

    private static Formula Characteristic(Formula characteristic, Formula cell,
        Formula reconstruction, Formula projection, int dimension)
    {
        var x = F.Id("x"); var y = F.Id("y");
        var disk = Call("Disk",F.D((byte)dimension));
        return And(Call("Continuous",characteristic),
            All("x",disk,Eq(Apply(cell,Call("val",x)),Apply(projection,Apply(reconstruction,x)))),
            All("x",disk,All("y",disk,Implies(Call("mem",Call("val",x),Ball(dimension)),
                Implies(Eq(Apply(characteristic,y),Apply(characteristic,x)),Eq(y,x))))));
    }

    private static Formula Chart(Formula cell, int dimension) =>
        And(Eq(Call("source",cell),Ball(dimension)),
            Call("ContinuousOn",cell,ClosedBall(dimension)),
            Call("ContinuousOn",Call("inverse",cell),Call("target",cell)));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Apply(Formula fn, params Formula[] args) => new Formula.Apply(fn,[.. args]);
    private static Formula Image(Formula fn, Formula set) => Call("image",fn,set);
    private static Formula Ball(int n) => Call("Ball",F.D((byte)n));
    private static Formula ClosedBall(int n) => Call("ClosedBall",F.D((byte)n));
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(left,FormulaLogicOperator.Or,right);
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(left,FormulaLogicOperator.Iff,right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left,FormulaLogicOperator.Implies,right);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left,FormulaRelationOperator.Equal,right);
    private static Formula Ne(Formula left, Formula right) => new Formula.Logic(Eq(left,right),FormulaLogicOperator.Implies,F.Id("False"));
}
