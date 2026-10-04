using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CatalanPowerHankel;

internal sealed class CiglerElevenReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenReduction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/cigler2023catalanpowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A triangular change of polynomial coordinates separates remainders modulo v from the first d coefficients.",
        H("Mixed Remainder and Coefficient Coordinates"),
        Blocks(
            Node("cigler-eleven-reduction-coordinates", "The coordinate determinant multiplier", "coordinate_change",
                "Let k be a nonnegative integer, let d be a positive integer, let v be a monic rational polynomial of degree k, and let Q_i be any k+d rational polynomials. Form a square matrix with entry [X^j](Q_i mod v) for columns j less than k and entry [X^(j-k)]Q_i for the remaining columns. Its determinant is v(0)^d times the determinant of the coefficient matrix with entry [X^j](Q_i mod (X^d v)) for all columns from zero through k+d-1. Remainders mean polynomial remainders on division by a monic polynomial. The monic basis 1,X,...,X^(k-1),v,Xv,...,X^(d-1)v makes the coordinate transformation block triangular with an identity block and a multiplication block of determinant v(0)^d. No nonzero constant coefficient is required.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
