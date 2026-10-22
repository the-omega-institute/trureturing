using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GaussZeroBalanced;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero-balanced Gauss quotients", H("Definitions and parameter classifications"), Blocks(
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-gauss"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Defs.gauss"),
                H("The Gauss hypergeometric function"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a, b, c and x, gauss a b c x is Mathlib ordinaryHypergeometric over the real numbers. Its defining coefficients are the ascending Pochhammer products divided by the denominator product and the factorial."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-quot"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Defs.quot"),
                H("The zero-balanced quotient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a, b and x, quot a b x is gauss (a+1) (b+1) (a+b+1) x divided by gauss a b (a+b) x."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-f"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Defs.f"),
                H("The contiguous quotient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a, b and x, f a b x is gauss a b (a+b+1) x divided by gauss a b (a+b) x."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-ineq17"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Defs.ineq17"),
                H("The shifted-parameter comparison"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a and r, ineq17 a r compares gauss (a+1) (2-a) 2 r / gauss a (1-a) 1 r strictly above gauss (a+1) (5/2-a) (5/2) r / gauss a (3/2-a) (3/2) r."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Defs.claim"),
                H("The two parameter classifications"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first clause quantifies over all positive real a and b: the derivative in b of quot a b x is strictly negative at every real x in (0,1) if and only if b is at most sqrt(a(a+1)). The second clause quantifies over every real a in (0,1): ineq17 a r holds at every real r in (0,1) if and only if a is at least 3/7."))), DescribeRole.Definition))));
}
