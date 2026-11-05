using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class TruncatedTetrahedronLowerCWDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Gluing/TruncatedTetrahedronLowerCW.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Midpoint subdivision gives an actual finite CW structure on the edge locus of the original truncated quotient for every finite raw face pairing.",
        H("Lower cells of the original truncated quotient"),
        Blocks(
            Describe.Lean(DescribeId.Create("lower-geometry"),
                DeclarationHandle.Create(Prefix + "lower_geometry"),
                H("Finite vertices, halfedges and cap edges"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let T be an arbitrary finite type with a topology and a DiscreteTopology instance. Let P be a RawFacePairing T, with its fixed-point-free involution of tagged faces and mutually inverse permutations of their three slots. The type T is allowed to be empty. The construction uses exactly TruncatedTetrahedronRelativeCW.TruncatedQuotient P, its original quotient topology, its original full equivalence closure, and the original projection q P. No edge-orientation hypothesis or pre-existing lower cell structure is assumed.")),
                    Paragraph(Text("A HalfOccurrence consists of a tag t and two distinct ordered coordinates i,j. The point halfPoint(h,r) has coordinates r at i, 1-r at j and zero at the other two positions, with r in [1/2,3/4]. The old endpoint oldPoint h is r=3/4; midPoint h is r=1/2. OldVertex and MidVertex are the finite quotients of these occurrences by equality of their respective q-images. Vertex is their disjoint sum. The function vertexPoint sends a class to that actual quotient point. Its injectivity includes disjointness between old vertices and midpoint vertices.")),
                    Paragraph(Text("Each OldVertex class also indexes one retained halfedge. Its representative h determines halfCharacteristic(v,z)=q(halfPoint(h,5/8+z(0)/8)) on Disk 1. Here Disk n is the closed unit ball in Fin n -> R with its original subtype topology. The map sends the two sphere points to an old vertex and a midpoint. Equality of q-images transports every coordinate by a permutation; the maximum coordinate therefore recovers the halfedge parameter. The characteristic map is injective on its entire closed disk, even when a raw face pairing reverses an original retained edge.")),
                    Paragraph(Text("The uniform transport theorem of FiniteZeroGuardedClosure supplies a coordinate permutation together with a zero footprint that works uniformly for every retained coordinate vector vanishing on that footprint. The consumed half_transport and half_fiber helpers specialize that existing theorem. The distinct values at an old endpoint recover the ordered support; using the same footprint transports the entire closed halfedge. In the open halfedge, equality of quotient points determines both the parameter and the old-vertex class. These helpers are applications of the existing transport result, not separate mathematical contributions.")),
                    Paragraph(Text("A CapOccurrence consists of a tag t, its cap corner u and a distinct zero face f. capFrame orders the two remaining coordinates. capPoint(c,z) has values 3/4 at u, zero at f, and (1+z(0))/8 and (1-z(0))/8 at those remaining coordinates. capMate transports the tag, corner and zero face through the actual raw pairing. capSetoid identifies exactly c with c or capMate c; CapEdge is its finite orbit quotient. The cap characteristic map uses one representative per actual pairing orbit.")),
                    Paragraph(Text("An open cap-edge point has exactly one zero coordinate. The full ambient face-fiber law from TruncatedTetrahedronCellGeometry applies to it. The existing hex_same_face_fiber lemma proves that a quotient identification within the chosen closed cap segment is trivial whenever one parameter is interior: an identification with its paired side would fix a tagged zero face, contradicting pairFixedFree. Thus the cap chart is a genuine open interval chart. Its two boundary endpoints may still be identified, as permitted for a CW characteristic map.")),
                    Paragraph(Text("vertexCell, halfCell and capCell use the existing diskPartial constructor. It extends each native q-composite to a PartialEquiv on the surrounding real coordinate space, with source the open unit ball. Continuity holds on the entire closed ball, and the inverse is continuous on the open target. For vertices the zero-dimensional disk is a singleton; for halfedges the closed characteristic map is injective; for cap edges the open fiber condition comes from the original full ambient relation. Compactness and Hausdorffness are those already established for the original quotient.")),
                    Paragraph(Text("Edge is OldVertex plus CapEdge. LowerCell n is the sum of vertices equipped with n=0 and edges equipped with n=1. lowerMap uses the corresponding vertex or edge chart after that equality. Every indexing type is finite; all cells are empty for n at least two. The pairwise-disjointness proof ranges over all pairs of dimensions. It uses injective vertex images, distinct halfedge endpoint classes, actual cap pairing orbits, the strict halfedge maximum below 3/4, and the distinction between one and two zero coordinates. It therefore covers vertex-edge collisions as well as collisions between different edges.")),
                    Paragraph(Text("Each one-cell sphere maps to the range of vertexPoint. A halfedge has the original endpoint and its midpoint. A cap-edge endpoint has the original coordinate pattern 3/4,1/4,0,0. The zero-cell sphere is empty. edgeSkeleton is the union of the finite vertex range and all closed edge images in the original quotient. lowerCW is the actual CWComplex.mkFinite construction on this subset, using the maps, all-dimensional disjointness, sphere attachment and exact closed cover. The finite_cw clause supplies this very construction, equality with lowerCW, and CWComplex.Finite for it.")),
                    Paragraph(Text("The edge locus has an independent description in the original four coordinates. originalEdges consists of points with either two distinct zero coordinates, or a coordinate equal to 3/4 and a distinct zero coordinate. The original_locus clause is edgeSkeleton P = q P '' originalEdges. The reverse inclusion reconstructs a two-zero point in one of the two closed retained halves, or reconstructs a cap point in its explicit closed segment. It then transports that segment to the chosen representative of its actual orbit. The forward inclusion verifies the coordinate conditions for every native vertex and closed edge point.")),
                    Paragraph(Text("The displayed LowerGeometry predicate expands to eleven clauses: existence of the specified finite CW structure; absence of cells in dimensions at least two; the exact original-coordinate image equality; the halfedge and cap q-composite formulas on every closed disk point; injectivity of vertexPoint; source equal to the open ball for every cell; continuity on every closed ball; inverse continuity on every open target; pairwise disjointness of open images over all dimensions; and one-cell sphere attachment to the actual vertex range. The projection argument in that predicate is supplied as the original q. The symbols in the displayed formula denote these exact Lean definitions, and the instance brackets retain all finite and topological dictionaries from the theorem telescope.")),
                    Paragraph(Text("The construction is derived for this repository's concrete guarded quotient. Mathlib's finite CW constructor supplies the finite weak-topology step after the explicit geometric obligations are proved. The existing upper_geometry theorem supplies the independently constructed upper charts and relative three-cells. Assembling the full absolute two- and three-dimensional CW complex remains a subsequent target; this theorem constructs only the coherent lower-cell prerequisite. It does not assert an Euler invariant or completion of the wider CFMP programme."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var t = F.Id("T");
        var p = F.Id("P");
        return All("T", F.Id("Types"),
            F.Seq(F.OpenBracket, Call("Fintype", t), F.CloseBracket, F.Sp,
                F.OpenBracket, Call("TopologicalSpace", t), F.CloseBracket, F.Sp,
                F.OpenBracket, Call("DiscreteTopology", t), F.CloseBracket, F.Sp,
                All("P", Call("RawFacePairing", t), Call("LowerGeometry", p, Call("q", p)))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
