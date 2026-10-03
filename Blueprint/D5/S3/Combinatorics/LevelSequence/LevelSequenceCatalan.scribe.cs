using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.LevelSequence;

internal sealed class LevelSequenceCatalanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LevelSequence/LevelSequenceCatalan.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/mansour2026wilf");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The level sequences avoiding 101 and 102 are counted by the Catalan numbers.",
        H("Catalan Enumeration of Level Sequences"),
        Blocks(
            Node("level-sequence-levelsequencecatalan-result", "The Catalan enumeration", "result",
                "For every positive n, the number of level sequences of length n avoiding 101 and 102 equals the Catalan number at index n.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("mansour-level-sequences-101-102-catalan"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
