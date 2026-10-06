using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class TripleAvoidingMatchingsEncodingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three distinct actions record openings and the two possible closing ranks of an avoiding matching.",
        H("Encoding matchings by labeled scan actions"),
        Blocks(
            Node("bss-encoding-action", "The three scan actions", "Action",
                "The alphabet has three distinct letters: opening, oldest and second. The last two distinguish closing the oldest open arc from closing the second-oldest open arc, including when only two arcs are open.", DescribeRole.Definition),
            Node("bss-encoding-encode", "The scan word of a matching", "encode",
                "At each vertex, record opening if its partner lies to the right. Otherwise record second if some older arc remains open at that vertex, and oldest if no such older arc exists. For a P1-avoiding matching these labels specify the exact closing rank.", DescribeRole.Definition),
            Node("bss-encoding-encode-injective", "The scan word determines an avoiding matching", "encode_injective",
                "Two P1-avoiding perfect matchings on the same 2n ordered vertices are equal whenever their encoded action words are equal. The order of the open arcs determines each closing partner from its action label.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
