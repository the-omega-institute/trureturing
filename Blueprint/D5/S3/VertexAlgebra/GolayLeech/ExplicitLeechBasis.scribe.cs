using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GolayLeech;

internal sealed class ExplicitLeechBasisDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechBasis.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit Golay-congruence lattice mathematics.",
        H("Exact integral construction"),
        Blocks(
            Describe.Lean(DescribeId.Create("result-0"),
                DeclarationHandle.Create(Prefix + "finite_column_certificate"), H("Literal basis columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each of the twenty-four integer columns has a supplied explicit binary message and the required parity and sum congruences. All column identities are kernel checked."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-1"),
                DeclarationHandle.Create(Prefix + "finite_generator_coordinates"), H("Integer generator coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sixty original generators are eight times each unit coordinate, twenty-three four-times differences, twice each polynomial generator and the odd vector (-3,1,...,1). Literal integer coordinates in the supplied basis are checked by matrix multiplication."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-2"),
                DeclarationHandle.Create(Prefix + "finite_gram_certificate"), H("Integral Gram identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal Gram matrix satisfies B-transpose times B equals eight times G. Symmetry and even diagonal are checked entrywise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result-3"),
                DeclarationHandle.Create(Prefix + "gram_determinant"), H("Unit Gram determinant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The triangular integer basis has determinant two to the thirty-sixth power. Taking determinants in the exact scaled Gram identity proves determinant G equals one; no positive or unimodular matrix is assumed."))), DescribeRole.Theorem))));
}
