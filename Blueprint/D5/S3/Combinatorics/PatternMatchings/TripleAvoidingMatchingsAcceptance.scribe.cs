using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class TripleAvoidingMatchingsAcceptanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsAcceptance.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scan of every P1-avoiding perfect matching obeys the height and phase transitions.",
        H("Avoiding matchings yield accepted scan words"),
        Blocks(
            Node("bss-acceptance-encode-accepted", "Acceptance of the encoded matching", "encode_accepted",
                "For every P1-avoiding perfect matching on 2n ordered vertices, its encoded action word is accepted from height zero in the normal phase. The pending oldest closure persists through all intervening openings and disappears when that oldest arc closes.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
