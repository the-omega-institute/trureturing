using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class TruncatedTetrahedronCellGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Gluing/TruncatedTetrahedronCellGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original retained quotient has exact ambient fibers and complete closed ball reconstructions.",
        H("Retained tetrahedron cell geometry"),
        Blocks(
            Describe.Lean(DescribeId.Create("cell-geometry"),
                DeclarationHandle.Create(Prefix + "cell_geometry"),
                H("Full fibers and reconstruction of every closed cell"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Quantify over every universe-level type T, every Fintype T dictionary finiteT, every topology topologyT on T, every DiscreteTopology T topologyT dictionary discreteT, and every RawFacePairing P on T. T may be empty. The pairing consists of the original fixed-point-free involution P.facePair on T times Fin 4 and the mutually inverse three-slot permutations P.faceMap. These are the complete theorem inputs; no quotient topology or cell structure is supplied.")),
                    Paragraph(Text("The retained-quotient definitions use the namespace TruncatedTetrahedronRelativeCW. TruncatedPoint T is exactly ActualLinkAffineFan.TruncatedPoint T, namely T times the subtype of four real coordinates in [0,3/4] with sum one. Its topology is the original product and subtype topology. The frame and sigma maps are those of RawFaceLinkPathConnected. truncatedMove P f transports the tag by P.facePair and all four coordinates by inverse sigma. TruncatedStep P a b means that some coordinate f of a is zero and b is that transported point. TruncatedQuotient P is the quotient by the entire Relation.EqvGen of this step, with its original quotient topology. q P is the original Quotient.mk' projection.")),
                    Paragraph(Text("Interior a means that all four coordinates of a are nonzero. FaceInterior a f means that coordinate f is zero and every zero coordinate is f. The first clause quantifies over every a and b in the full retained carrier: if Interior a, equality of their quotient projections is equivalent to b=a. The second clause also quantifies over every f in Fin 4: if FaceInterior a f, its transported mate differs from a and equality of projections is equivalent to b=a or b=truncatedMove P f a. This includes self-pairings of faces in one tetrahedron. No restriction to one face or to the interior is imposed on b.")),
                    Paragraph(Text("Disk d is the subtype of the closed unit ball centered at zero in Fin d -> R, with its inherited topology. TruncatedTetrahedron is the original closed four-coordinate subtype without a tag. FaceShape has exactly hex and cap. faceCarrier k t j consists of all retained points with tag t and coordinate j equal to zero for hex, or 3/4 for cap; every lower-dimensional boundary tie is included.")),
                    Paragraph(Text("The bulk reconstruction clause gives, for each t in T, a homeomorphism h from the entire Disk 3 to the entire TruncatedTetrahedron such that bulkDiskPoint t x=(t,h x) for every x in Disk 3. The face reconstruction clause gives, for each k,t,j, a homeomorphism h from the entire Disk 2 onto the subtype faceCarrier k t j such that faceDiskPoint k t j x is the underlying retained point of h x for every disk point. These are equalities for the prescribed original reconstructions, not merely existence of some parametrizations. They imply full closed-carrier coverage, including all boundary points.")),
                    Paragraph(Text("For the proof, the original coordinate models retain three or two coordinates and recover the last as the prescribed mass minus their sum. The bulk and hex models have mass one, the cap model mass 1/4, and each retained coordinate lies in [0,3/4]. Closedness, compactness, convexity and nonempty strict interiors give Mathlib's ambient convex-body homeomorphism carrying the whole body, its interior and frontier to the closed ball, open ball and sphere. bulkHomeomorph and faceHomeomorph reconstruct the original coordinates. The two reconstruction witnesses are the composites of the inverse ball homeomorphisms with those actual affine homeomorphisms. The fiber proofs use the full original zero-guarded equivalence closure; the single-zero class consists exactly of the original point and its distinct transported mate.")),
                    Paragraph(Text("In the formula, Types denotes the chosen universe of types, Fintype(T) the finite enumeration dictionary type, TopologicalSpace(T) its topology type, and DiscreteTopology(T,topologyT) the corresponding discrete-topology dictionary type. Homeomorph(A,B) denotes A equiv_t B with the topologies just specified; pair(t,z) is the original product constructor, and val removes exactly one subtype layer. Every quantifier over a,b is over TruncatedPoint T, every f,j is in Fin 4, k is in FaceShape, and each disk quantifier includes its closed-ball subtype proof. The four displayed clauses are precisely CellGeometry P (q P).")),
                    Paragraph(Text("TruncatedTetrahedronRelativeCW.upper_geometry consumes the two fiber clauses directly. Its topCell_closed_image and directedFaceCell_closed_image proofs consume the two reconstruction witnesses through their surjectivity and pointwise equalities. The supplier also owns the unchanged compact/open chart machinery and original Hausdorff quotient argument used by that assembly. This theorem establishes the retained geometric input to the upper relative complex; an absolute CW structure and an Euler invariant require further results."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var t = F.Id("T"); var p = F.Id("P");
        var x = Call("TruncatedPoint",t); var q = Call("q",p);
        var a = F.Id("a"); var b = F.Id("b"); var f = F.Id("f");
        var tag = F.Id("t"); var k = F.Id("k"); var j = F.Id("j");
        var h = F.Id("h"); var z = F.Id("x");
        var move = Call("truncatedMove",p,f,a);
        var clauses = And(
            All("a",x,All("b",x,Implies(Call("Interior",a),
                Iff(Eq(Apply(q,a),Apply(q,b)),Eq(b,a))))),
            All("a",x,All("b",x,All("f",Call("Fin",F.D(4)),
                Implies(Call("FaceInterior",a,f),And(Ne(move,a),
                    Iff(Eq(Apply(q,a),Apply(q,b)),Or(Eq(b,a),Eq(b,move)))))))),
            All("t",t,Exists("h",Call("Homeomorph",Call("Disk",F.D(3)),F.Id("TruncatedTetrahedron")),
                All("x",Call("Disk",F.D(3)),
                    Eq(Call("bulkDiskPoint",tag,z),Call("pair",tag,Apply(h,z)))))),
            All("k",F.Id("FaceShape"),All("t",t,All("j",Call("Fin",F.D(4)),
                Exists("h",Call("Homeomorph",Call("Disk",F.D(2)),
                    Call("Subtype",Call("faceCarrier",k,tag,j))),
                    All("x",Call("Disk",F.D(2)),
                        Eq(Call("faceDiskPoint",k,tag,j,z),Call("val",Apply(h,z)))))))));
        return All("T", F.Id("Types"),
            F.Seq(F.OpenBracket, Call("Fintype", t), F.CloseBracket, F.Sp,
                F.OpenBracket, Call("TopologicalSpace", t), F.CloseBracket, F.Sp,
                F.OpenBracket, Call("DiscreteTopology", t), F.CloseBracket, F.Sp,
                All("P", Call("RawFacePairing", t), clauses)));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),domain,body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(name),domain,body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name),[.. args]);
    private static Formula Apply(Formula fn, params Formula[] args) => new Formula.Apply(fn,[.. args]);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i],FormulaLogicOperator.And,result);
        return result;
    }
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(left,FormulaLogicOperator.Or,right);
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(left,FormulaLogicOperator.Iff,right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left,FormulaLogicOperator.Implies,right);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left,FormulaRelationOperator.Equal,right);
    private static Formula Ne(Formula left, Formula right) => Implies(Eq(left,right),F.Id("False"));
}
