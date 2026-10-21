using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KummerRatio;

internal sealed class BetaIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Beta moments and integral formulas for the Kummer function.",
        H("Beta integral representation"), Blocks(
            Describe.Lean(DescribeId.Create("kummer-real-beta-integral"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta"),
                H("Real beta moments"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive real p and q, the integral over the unit interval of t raised to p minus one times one minus t raised to q minus one equals Gamma(p) Gamma(q) divided by Gamma(p+q). The complex beta identity transfers to this real integral because both bases are nonnegative on the integration interval."))),
                DescribeRole.Theorem))));
}
