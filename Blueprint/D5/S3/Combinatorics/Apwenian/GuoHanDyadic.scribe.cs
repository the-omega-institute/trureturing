using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Apwenian;

internal sealed class GuoHanDyadicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Apwenian/GuoHanDyadic.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/guo2025apwenian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Iterating the apwenian recursion expresses each entry as the sum over a consecutive interval of binary descendants.",
        H("Dyadic Expansion of the Apwenian Recursion"),
        Blocks(
            Node("guo-han-dyadic-expansion", "Sum over binary descendants", "dyadic_expansion",
                "For every sequence b in the integers modulo two satisfying b(n) = b(2n + 1) + b(2n + 2) for all nonnegative n, and every pair of nonnegative integers h and n, b(n) is the sum of b(2^h(n + 1) - 1 + j) over j from zero through 2^h minus one. The sum is taken modulo two. At depth zero it consists of b(n) alone; at each successive depth the two descendants of each term partition the next consecutive interval.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
