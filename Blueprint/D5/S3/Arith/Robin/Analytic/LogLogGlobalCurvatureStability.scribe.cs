using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class LogLogGlobalCurvatureStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvatureStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global stability transfers the log-log tangent gap across three clocks.",
        H("Log-Log Tangent-Gap Stability"),
        Blocks(
            Paragraph(Text(
                "The three-clock estimate separates the displacement of the reference clock from "
                    + "the endpoint gap. It combines the global quadratic sandwich with a mean-value "
                    + "bound for g(t)=1/(t log t), and remains valid for arbitrary real clocks above one.")),
            Describe.Lean(
                DescribeId.Create("loglog-tangent-gap-stability"),
                DeclarationHandle.Create(Prefix + "loglog_tangent_gap_stability"),
                H("Global three-clock stability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a,x,y>1, the absolute difference |K(a,x)-K(a,y)| is at most "
                        + "w(min(a,min(x,y))) times the sum of |y-a||x-y| and |x-y|²/2. "
                        + "The argument allows either ordering and equality of the clocks."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("loglog-tangent-gap-stability-scaled"),
                DeclarationHandle.Create(Prefix + "loglog_tangent_gap_stability_scaled"),
                H("Half-scale stability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When exp(2)<=a and a/2<=x,y, the same stability estimate is bounded by "
                        + "16/(a² log(a)) times the displacement expression. The theorem does not "
                        + "impose an upper endpoint restriction and does not assert an arithmetic "
                        + "or Robin/RH consequence."))),
                DescribeRole.Theorem))));
}
