using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicPadovanTriplesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicPadovanTriples.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated increasing low blocks cannot contribute letters to certain 213 triples.",
        H("Triples in Separated Blocks"),
        Blocks(
            Node("archer-cyclic-padovan-triple-high-low", "Triple before a low block", "triple_213_in_high",
                "If every high-block letter exceeds every letter of an increasing low block, any subsequence c, b, d with b less than c less than d lies entirely in the high block.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-triple-low-high", "Triple after a low block", "triple_213_after_low",
                "If an increasing low block precedes a block of larger letters, any subsequence c, b, d with b less than c lies entirely in the later high block.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
