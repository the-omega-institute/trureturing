using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SemiMeanderSecondDiagonal;

internal sealed class Stage3Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage3.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/hogan2026a400429");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connectivity of the joined half matchings excludes incompatible endpoint patterns.",
        H("Connectivity Constraints"),
        Blocks(
            Describe.Lean(DescribeId.Create("endpoints"),
                DeclarationHandle.Create(Prefix + "connected_endpoint_cases"),
                H("Connected endpoint cases"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A connected joined matching has only the endpoint configurations admitted by the local pairing classification."))),
                DescribeRole.Theorem)),
        []));
}
