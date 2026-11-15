using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class Verkama62EarGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/Verkama62EarGeometry.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/verkama2026connectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometry of an anchored two-vertex ear.",
        H("Geometry of an anchored two-vertex ear"),
        Blocks(
            Node("verkama62-eargeometry-pairear", "An induced three-edge ear", "PairEar",
                "The new positions u < v have pi(v) < pi(u). They have distinct old attachments x,y, respectively, and no other neighbours in S. Both new positions lie outside S.", DescribeRole.Definition),
            Node("verkama62-eargeometry-pairear-to-double", "The northeast orientation", "to_double",
                "Let S contain at least three points and the original leftmost point. Suppose the induced old stage remains connected after deleting each of its points. Every induced two-vertex ear has the northeast double-ear geometry, with its two new positions unchanged. Deleting an attachment puts all remaining old points on one common side of the corresponding new point. A common old point rules out opposite side choices. The southwest placement of the old points gives the required inequalities; the northeast placement contradicts the leftmost anchor. No pattern avoidance or triangle-freeness is assumed.", DescribeRole.Theorem),
            Node("verkama62-eargeometry-anchored-extension", "Extension of every proper anchored stage", "anchored_extension",
                "Assume the ambient value graph is connected after each single deletion and is connected. Let S contain at least three points, the original leftmost point z, and the original bottommost point b, with z distinct from b. Assume each old-point deletion leaves the induced old stage connected. If S is proper, there is an outside singleton with at least two old neighbours or a northeast double ear. If no singleton is available, every boundary point has a unique old attachment. Connectivity and connectivity after deleting that attachment give two distinct attachments. The two anchors force all other old points southwest of either boundary point. The two attachment inversions then have opposite orientations and form a two-vertex ear.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
