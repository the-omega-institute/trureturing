using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicTetranacciSuccessorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The successor permutation of an inserted word has an explicit low prefix and relabeled suffix.",
        H("Successors After Low-Arc Insertion"),
        Blocks(
            Node("archer-cyclic-relabel", "Relabel old successors", "relabel",
                "This map fixes zero, sends one to one when k is one and to two otherwise, and shifts every larger value upward by k.", DescribeRole.Definition),
            Node("archer-cyclic-low-prefix", "Low successor prefix", "lowPrefix",
                "The low prefix is two when k is one; otherwise it begins with k plus one, continues from three through k, and ends with one.", DescribeRole.Definition),
            Node("archer-cyclic-successor-insert", "Successor permutation after insertion", "oneLine_insert",
                "For a rooted permutation word and positive k, the successor permutation of its inserted word is the low prefix followed by the original successor permutation with its entries relabeled.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
