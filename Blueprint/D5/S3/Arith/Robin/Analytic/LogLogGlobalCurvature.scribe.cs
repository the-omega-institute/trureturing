using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class LogLogGlobalCurvatureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The log-log tangent gap is globally trapped by endpoint curvature.",
        H("Global Log-Log Curvature"),
        Blocks(
            Paragraph(Text(
                "For a,b>1, the tangent gap K(a,b)=log(log(a))+(b-a)/(a log(a))-log(log(b)) "
                    + "is nonnegative and is bounded above and below by the endpoint values of "
                    + "w(t)=(1+log(t))/(t² log(t)²) times (b-a)²/2. The endpoints may coincide "
                    + "or occur in either order.")),
            Describe.Lean(
                DescribeId.Create("loglog-tangent-gap-quadratic"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvature.loglog_tangent_gap_quadratic"),
                H("Full-domain quadratic tangent-gap sandwich"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof reuses ArithmeticMixedCornerResponse.density_antitone for the "
                        + "endpoint density bounds and applies the second-derivative convexity "
                        + "criterion to the two quadratic-corrected gaps. No displacement bound, "
                        + "integer specialization, prime estimate or Robin/RH conclusion is assumed."))),
                DescribeRole.Theorem))));
}
