using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq207DurfeeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq207Durfee.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partition diagrams split at their maximal square and produce the normalized pentagonal inverse series.",
        H("Durfee-Square Decomposition"),
        Blocks(
            Node("inversionseq207-durfee-durfee-square-normalization", "Durfee-square normalization", "durfee_square_normalization", "With the discrete topology on the rationals, the sum over natural sizes of q raised to the square of the size times the square of the inverse Euler denominator converges to the inverse of the pentagonal power series. The decomposition is obtained by removing the maximal square from each partition diagram and separating the right and bottom pieces.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
