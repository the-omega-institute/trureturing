using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicPadovanBijectionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicPadovanBijections.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Insertion branches partition the auxiliary and main classes of rooted avoiders.",
        H("Insertion Branches for Padovan Words"),
        Blocks(
            Node("archer-cyclic-padovan-high-insert", "Insert a high block", "highInsert",
                "This insertion keeps one first, raises the remaining letters above a low block, and appends two followed by the increasing letters from three through m.", DescribeRole.Definition),
            Node("archer-cyclic-padovan-aux-split", "Split the auxiliary class", "auxiliary_split",
                "For k at least two, the auxiliary words are exactly the union of front insertions into good words of size k and final low-block insertions of size two into auxiliary words of index k minus one.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-aux-card", "Auxiliary cardinality recurrence", "auxiliary_card_recurrence",
                "For k at least two, the number of auxiliary words of index k is the number of good words of size k plus the number of auxiliary words of index k minus one.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-main-split", "Split the main class", "main_split",
                "For n at least two, the good words of size n are exactly the union of front insertions into good words of size n minus one and high-block insertions into auxiliary words of indices one through n minus two.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
