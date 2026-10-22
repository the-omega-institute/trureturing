using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GaussZeroBalanced;

internal sealed class ComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singular endpoint comparison and the Riccati certificate", H("Comparison"), Blocks(
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-singular-comparison"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Comparison.singular_comparison"),
                H("Singular endpoint comparison"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A continuous function that vanishes at the left endpoint and satisfies a strict positive first order differential inequality x u' + P u > 0 on a positive interval is strictly positive in the interval when P is positive. The proof uses the minimum on a compact subinterval and handles both interior and right endpoint minima."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-certificate-identity"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Comparison.certificate_identity"),
                H("Riccati certificate identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a function satisfying the zero-balanced Riccati equation, differentiating E = q t f^2 + f - 1 with t = x/(1-x) gives x E' + c(1+2 q t f)E = q t^2 f^2(1-2 q f)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-certificate"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Comparison.certificate"),
                H("Positive Riccati certificate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive a, b and 0 < x < 1, the contiguous quotient satisfies (1-f)/(t f^2) < a b/((a+b)(a+b+1))."))), DescribeRole.Theorem)
        )));
}
