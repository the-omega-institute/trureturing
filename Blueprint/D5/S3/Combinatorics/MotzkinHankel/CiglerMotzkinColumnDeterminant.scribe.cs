using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinColumnDeterminantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Monic division transforms modified moment determinants, and fixed columns preserve the confluence order of the varying columns.",
        H("Remainder Determinants and Mixed Confluence"),
        Blocks(
            Node("cigler-motzkin-column-determinant-remainders", "Monic multiplier determinants", "multiplier_remainders",
                "Let R be a nontrivial commutative ring, let p_i be monic polynomials of degree i, and let ell be an R-linear functional with ell(p_i p_j) equal to one when i equals j and zero otherwise. For any monic polynomial g of degree h and any nonnegative n, the determinant of ell(g y^(i+j)) for indices i and j below n equals (-1)^(nh) times the h by h determinant whose entry in row i and column j is the coefficient of y^j in the remainder of p_{n+i} modulo g. Integral triangular changes of basis and monic division give the identity, including empty matrices.", DescribeRole.Theorem),
            Node("cigler-motzkin-column-determinant-confluence", "Confluence with fixed columns", "mixed_confluence",
                "Let R be a commutative ring and m and k be nonnegative integers. Choose formal series f_i(y) for rows i below m + k, scalars c_j for j below m, and fixed entries g_{i,j} for j below k. Form A(y) with first m columns f_i(c_j y) and last k columns g_{i,j}. Form J with first m columns the coefficients of y^j in f_i and the same last k columns. Every coefficient of det A below binom(m,2) vanishes, and its coefficient at binom(m,2) is det Vandermonde(c) times det J. Expansion along the fixed columns reduces the formula to alternant confluence.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
