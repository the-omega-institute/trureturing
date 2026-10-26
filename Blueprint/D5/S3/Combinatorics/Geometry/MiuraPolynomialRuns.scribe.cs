using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraPolynomialRunsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational weights for simultaneous positive run lengths.", H("Rational weights for simultaneous positive run lengths"),
        Blocks(
            Describe.Lean(DescribeId.Create("miurapolynomialruns-0"),
                DeclarationHandle.Create(Prefix + "falling"), H("One shifted falling product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In either dimension variable, multiply k successive linear factors shifted by the occupied-axis count plus one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miurapolynomialruns-1"),
                DeclarationHandle.Create(Prefix + "runPolynomial"), H("A rational binomial weight"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Divide the shifted falling product of length r-1 by the factorial of r-1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miurapolynomialruns-2"),
                DeclarationHandle.Create(Prefix + "jointRunPolynomial"), H("Both axes in one polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply the row weight in the first variable by the column weight in the second variable."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miurapolynomialruns-3"),
                DeclarationHandle.Create(Prefix + "joint_run_polynomial_eval"), H("Exact positive-vector cardinality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive run counts r,s and dimensions satisfying u+r at most m and v+s at most n, evaluating the polynomial at m,n equals the cardinality of the actual Cartesian product of positive row-run vectors of total m-u and positive column-run vectors of total n-v. The falling-factorial evaluation is the rational binomial identity. This statement counts positive vectors; identifying these vectors with a fiber of height functions requires a separate bijection."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miurapolynomialruns-4"),
                DeclarationHandle.Create(Prefix + "joint_run_polynomial_degree_le"), H("The degree is bounded by both run exponents"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive r,s, the total degree is at most r+s-2. Each axis supplies r-1 or s-1 linear factors, and multiplication adds these bounds."))), DescribeRole.Theorem))));
}
