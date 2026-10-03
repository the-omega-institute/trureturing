using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PermutationSquare;

internal sealed class PermutationSquareCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PermutationSquare/PermutationSquareCounting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Dynamics/archer2026pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing the final decreasing component gives a four-term recurrence with the number of indecomposable square-avoiders as its additional term.",
        H("The corrected counting recurrence"),
        Blocks(
            Node("permutationsquarecounting-count-recurrence-theorem", "Counting by the final component", "count_recurrence", "For every natural number n at least five, a(n) equals a(n minus one) plus a(n minus two) plus a(n minus three) plus a(n minus four) plus b(n), where b(n) counts the permutations of one through n that avoid 312 and 54321, have squares avoiding 132, and are indecomposable under direct sum. Each decomposable permutation has a final decreasing component of length one, two, three or four; deleting it leaves a nonempty permutation in the same square-avoidance class. These four possibilities and the indecomposable permutations partition the class.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
