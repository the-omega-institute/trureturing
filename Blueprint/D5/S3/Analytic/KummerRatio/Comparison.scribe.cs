using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KummerRatio;

internal sealed class ComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Comparison of positive solutions of the confluent hypergeometric equation.",
        H("Logarithmic derivatives and finite parameter increments"), Blocks(
            Describe.Lean(DescribeId.Create("kummer-positive-solution-family"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/Comparison.SolutionFamily"),
                H("Positive regular solution families"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A solution family consists of y, its first derivative and its second derivative. For every positive parameter s, the function y(s,x) is positive on the closed positive ray, y and its first derivative are continuous there, the two derivative identities hold on the positive ray, and x y''+(c-x)y'-s y=0."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kummer-positive-solution-ratio"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/Comparison.solution_ratio_strictAntiOn"),
                H("Strict decrease for a positive solution family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let c be positive. For every positive parameter s, let y(s,x) be positive for x at least zero, with y and its first derivative continuous there, twice differentiable at every positive x, and satisfying x y''+(c-x)y'-s y=0. For positive delta and 0<a<b, the quotient y(b+delta,x)y(a,x)/(y(a+delta,x)y(b,x)) strictly decreases on the positive ray. The normalization at zero is arbitrary.")),
                    Paragraph(Text("Put h(s,x)=y'(s,x)/y(s,x). The Riccati equation and the weight x^c exp(-x)y(u,x)y(v,x) show that h(v,x)>h(u,x) whenever 0<u<v and x>0. The weight vanishes continuously at zero. A second weighted identity shows that h(b+delta,x)-h(b,x) is strictly less than h(a+delta,x)-h(a,x). This is the logarithmic derivative of the quotient, and the quotient is positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kummer-upper-parameter-strict-decrease"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/Comparison.ratio_strictAntiOn"),
                H("Strict decrease of the Kummer ratio"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For c>0, delta>0 and 0<a<b, the quotient M(b+delta;c;x)M(a;c;x)/(M(a+delta;c;x)M(b;c;x)) strictly decreases for x>0. The entire defining series supplies the differential equation and the continuous derivatives. Nonnegative coefficients give M(s;c;x) at least one for positive s and nonnegative x, so the general positive solution comparison applies."))),
                DescribeRole.Theorem))));
}
