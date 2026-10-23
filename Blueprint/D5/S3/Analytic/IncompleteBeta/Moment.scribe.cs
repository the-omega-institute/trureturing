using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.IncompleteBeta;

internal sealed class MomentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite convolution and beta moment kernel for incomplete beta coefficients.",
        H("Moment kernel"), Blocks(
            Describe.Lean(DescribeId.Create("incomplete-beta-convolution"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta/Moment.convolution"),
                H("Finite coefficient convolution"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The convolution sums products of the Gamma coefficients at complementary indices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("incomplete-beta-w"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta/Moment.W"),
                H("Symmetric beta kernel"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite kernel is the sum of the two powered factors divided by the corresponding Gamma factors."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("incomplete-beta-moment"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta/Moment.convolution_eq_betaMean"),
                H("Beta moment representation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive a, s and t, the finite coefficient convolution is Gamma(2a+s+t+n) divided by Gamma(s)Gamma(t), times the integral from zero to one of u^(s-1)(1-u)^(t-1)W(u). Dividing the integral by the beta normalizer gives the normalized beta mean with a common factor depending only on s+t."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incomplete-beta-continuity"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta/Moment.W_continuousOn"),
                H("Continuity of the kernel"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive a and every natural n, the finite kernel is continuous on the closed unit interval, since all its power exponents are positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incomplete-beta-symmetry"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta/Moment.W_symm"),
                H("Reflection symmetry"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reflection about one half leaves W unchanged; reversal of the finite summation interchanges the two powers and their Gamma factors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incomplete-beta-derivative"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta/Moment.W_hasDerivAt"),
                H("Telescoping derivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the open unit interval, the derivative of W is u^(a-1)(1-u)^(a+n)/(Gamma(a)Gamma(a+n+1)) minus u^(a+n)(1-u)^(a-1)/(Gamma(a+n+1)Gamma(a)). The product rule and the Gamma recurrence give adjacent terms whose finite sum telescopes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incomplete-beta-monotonicity"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta/Moment.W_strictMonoOn"),
                H("Strict increase toward the midpoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive a, W is strictly increasing on the closed interval from zero to one half. Its derivative is strictly positive in the interior; continuity supplies the endpoints."))),
                DescribeRole.Theorem))));
}
