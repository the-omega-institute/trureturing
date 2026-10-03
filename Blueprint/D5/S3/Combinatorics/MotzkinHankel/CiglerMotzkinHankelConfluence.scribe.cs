using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinHankelConfluenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelConfluence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first possible coefficient of a rescaled alternant is a Vandermonde determinant times a coefficient determinant.",
        H("Integral Confluence of Formal Alternants"),
        Blocks(
            Node("cigler-motzkin-hankel-confluence-alternant", "The first alternant coefficient", "alternant_coefficients",
                "Let R be any commutative ring, let m be a nonnegative integer, let f_i(y) be m formal power series over R, and let c_j be m elements of R, with indices starting at zero. Form the matrix with entry f_i(c_j y). Every coefficient of its determinant at an index below binom(m,2) is zero. The coefficient at index binom(m,2) equals the determinant of the Vandermonde matrix with entry c_i^j times the determinant of the matrix with entry the coefficient of y^j in f_i(y). The formula imposes no distinctness condition on the c_j and requires no division by factorials or differences of parameters.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
