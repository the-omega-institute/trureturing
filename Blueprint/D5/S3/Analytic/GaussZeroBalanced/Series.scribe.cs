using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GaussZeroBalanced;

internal sealed class SeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Gauss series and the Riccati equation", H("Series identities"), Blocks(
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-one-le-gauss"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Series.one_le_gauss"),
                H("Lower bound by the constant term"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive real a, b and c and 0 <= x < 1, gauss a b c x is at least one. All coefficients and all terms are nonnegative, and the constant term is one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-gauss-pos"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Series.gauss_pos"),
                H("Positivity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive real a, b and c and 0 <= x < 1, gauss a b c x is strictly positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-hasDerivAt-gauss"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Series.hasDerivAt_gauss"),
                H("Differentiation in the argument"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive real a, b and c and 0 <= x < 1, the derivative of gauss a b c at x is (a*b/c) times gauss (a+1) (b+1) (c+1) x. At zero this is a two-sided derivative. A radius strictly between abs(x) and one supplies a summable majorant for the termwise derivatives."))), DescribeRole.Theorem)))));
}
