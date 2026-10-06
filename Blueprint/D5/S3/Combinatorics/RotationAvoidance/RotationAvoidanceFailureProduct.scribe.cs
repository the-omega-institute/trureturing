using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceFailureProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFailureProduct.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated alternating circles factor into two Fibonacci enumerations.",
        H("RotationAvoidanceFailureProduct"),
        Blocks(
            Node("rotationavoidancefailureproduct-alternatingseparatedcirclecount", "Separated alternating circle count", "alternating_separated_circle_count", "For a pivot between two and size minus one, consider circular avoiders of 2413 rooted at pivot whose tail is all entries below pivot followed by all entries above pivot. Their number is the product of the Fibonacci numbers with indices twice pivot minus three and twice size minus pivot minus one.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

