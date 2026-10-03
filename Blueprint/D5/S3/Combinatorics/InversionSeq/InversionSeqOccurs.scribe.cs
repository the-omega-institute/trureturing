using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeqOccursDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeqOccurs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Occurrences of length-three patterns are characterized by three positions and their pairwise comparisons.",
        H("Occurrences of Length-Three Patterns"),
        Blocks(
            Node("inversionseq-inversionseqoccurs-occurs-three-iff", "Three-position characterization", "occurs_three_iff",
                "Let a, b and c be positive integers containing every rank from one through their maximum. The pattern with entries a, b and c occurs in a word if and only if there are three strictly increasing positions in the word whose entries have exactly the same pairwise strict inequalities and equalities as a, b and c.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
