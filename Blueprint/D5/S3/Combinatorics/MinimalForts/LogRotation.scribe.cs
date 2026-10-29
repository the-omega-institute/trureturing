using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class LogRotationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/LogRotation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic block rotation.",
        H("The logarithmic block rotation"),
        Blocks(
            Node("ratio-irrational", "Irrational logarithmic ratio", "ratio_irrational", "The ratio log(2/3) divided by log(4/3) is irrational. A rational equality would force equal positive integer powers of two and three, contradicted modulo two. Both logarithms are the actual real natural logarithms. This supplies the irrationality hypothesis for feasible multiplicity approximation.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
