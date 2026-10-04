using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CylindricPartition;

internal sealed class LiUncuRectangleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CylindricPartition/LiUncuRectangle.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QSeries/li2025macmahon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian polynomials enumerate weakly decreasing tuples by their total size.",
        H("Gaussian Enumeration of Rectangles"),
        Blocks(
            Node("li-uncu-rectangle-gauss-rectangle", "The rectangle enumerator", "gauss_rectangle",
                "For all nonnegative integers M and m, G(M+m,m) is the sum of q raised to the sum of the entries over all weakly decreasing tuples of m entries between zero and M. Thus it enumerates partitions contained in a rectangle of width M and height m.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
