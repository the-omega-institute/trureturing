using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class LogRotationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/LogRotation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic block rotation.",
        H("The logarithmic block rotation"),
        Blocks(
            Node("block-logarithm-window", "Uniform approximation for the block increments", "block_logarithm_window", "The increment is the natural logarithm of two thirds and the positive period is the natural logarithm of four thirds. Their ratio is irrational: a rational ratio would force equal positive integer powers of two and three, contradicted by reduction modulo two. Consequently every positive error tolerance has one threshold for all larger positive integer windows and every real target. The conclusion gives actual integers x and z and the real error bound, without assuming any graph count.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
