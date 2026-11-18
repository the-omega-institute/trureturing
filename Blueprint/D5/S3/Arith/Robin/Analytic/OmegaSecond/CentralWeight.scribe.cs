using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class CentralWeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-weight quadrature with endpoint errors and the total variation of the weight.",
        H("Uniform central prime-weight comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-quadrature-upper"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralWeight.prime_quadrature_upper"),
                H("Finite prime quadrature upper bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On every real interval [a,b] with 0<=a<=b, let d be continuous and let f have derivative d throughout the interval. If abs(primeCount(t)-C*t)<=E there for E>=0, the prime sum of f over a<p<=b is at most C times the integral of f plus E*(abs(f(a))+abs(f(b))+the integral of abs(d)), with E multiplying the entire parenthesized expression. Both endpoints and the full variation are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("central-prime-weight-upper"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralWeight.central_prime_weight_upper"),
                H("Uniform moving-weight comparison"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every sufficiently large real P, the estimate holds for every s>=0: the localized prime-weight sum over P/2<p<=2P is at most its real integral over [P/2,2P] divided by log(P), plus 112*log(2)*P/log(P)^2.")),
                    Paragraph(Text("The weight increases up to P and decreases after P, so its total variation is bounded independently of s. This prevents the error from growing with the moving saddle. This is an upper estimate; a matching lower counting bound at the second threshold is not established here."))),
                DescribeRole.Theorem))));
}
