using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicTetranacciOneLineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicTetranacciOneLine.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first four low-arc insertions preserve one-line avoidance of 4123.",
        H("One-Line Avoidance Under Insertion"),
        Blocks(Node("archer-cyclic-insert-4123", "Pattern occurrence under insertion", "contains_4123_insert_iff",
            "For a rooted permutation word, inserting a low arc of length one through four produces a successor permutation containing 4123 exactly when the original successor permutation contains 4123.",
            DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
