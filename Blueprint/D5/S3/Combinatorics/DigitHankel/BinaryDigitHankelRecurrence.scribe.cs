using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class BinaryDigitHankelRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelRecurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary-carry reflection relates the Hankel determinant and a bordered difference determinant at complementary sizes.",
        H("Paired Reflection Recurrences"),
        Blocks(
            Node("binary-digit-hankel-recurrence-endpoint", "The bordered difference determinant", "endpoint",
                "For a nonnegative integer n and an integer t, E(n,t) is the determinant of the n by n matrix whose entry in row i and column j is S(i+j+1,t) - S(i+j,t) when j + 1 is less than n, and is one in the final column. Indices range from zero to n minus one. The determinant of the empty matrix is one.", DescribeRole.Definition),
            Node("binary-digit-hankel-recurrence-reflection", "Reflection of both determinants", "reflection",
                "For integers k at least one and n at least five satisfying 2^k < n and n at most 3 times 2^(k-1), and every integer t, put m = 2^(k+1) - n + 1, a = 2n - 2^(k+1) - 1, and u = t^(k+1) - 2t^k. Then H(n,t) = (-1)^(n+1) u^a H(m,t) + (t^k)^2 u^(a-1) E(m,t), and E(n,t) = (-1)^n u^a E(m,t). Here a is at least one. A binary-carry change of basis of determinant one gives a sparse matrix, and paired elimination yields both identities without dividing by u.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
