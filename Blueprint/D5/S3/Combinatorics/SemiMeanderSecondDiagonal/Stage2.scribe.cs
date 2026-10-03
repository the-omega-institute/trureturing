using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SemiMeanderSecondDiagonal;

internal sealed class Stage2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/hogan2026a400429");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prefix data reconstructs the two half matchings and joins their unmatched endpoints in rank order.",
        H("Prefix Reconstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("rank-join"),
                DeclarationHandle.Create(Prefix + "crossing_eq_rankJoin"),
                H("Crossing arches follow rank"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The cross-half arches of an upper matching pair unmatched endpoints according to their ranks in the two midpoint cuts."))),
                DescribeRole.Theorem)),
        []));
}
