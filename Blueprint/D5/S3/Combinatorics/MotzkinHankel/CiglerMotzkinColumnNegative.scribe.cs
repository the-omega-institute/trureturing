using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinColumnNegativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnNegative.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform horizontal weights give a negative-index vanishing interval and a unit determinant at its next endpoint.",
        H("The Negative-Index Unit Endpoint"),
        Blocks(
            Node("cigler-motzkin-column-negative-endpoint", "Vanishing and the first unit determinant", "negative_endpoint",
                "Let h be nonnegative and let g(y) be monic of degree h over the integer polynomial ring in t. Specialize s to t in the orthogonal polynomials p_r and the backward polynomials b_r, where b_0 = s - t, b_1 = (y - t)b_0 - 1 and b_{r+2} = (y - t)b_{r+1} - b_r. For each gap from one through h, form an h by h coefficient matrix with row polynomial b_{gap-1-i} when i is below gap and p_{i-gap} otherwise, taking remainders modulo g and coefficients of y^j in column j. Its determinant is zero. The matrix with row polynomial b_{h-i} modulo g has determinant (-1)^binom(h+1,2). After specialization b_0 vanishes and b_{r+1} = -p_r, so a zero row gives the gap and reversed monicity gives the endpoint.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
