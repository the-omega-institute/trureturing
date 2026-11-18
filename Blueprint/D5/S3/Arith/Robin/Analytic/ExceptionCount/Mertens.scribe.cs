using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.ExceptionCount;

internal sealed class MertensDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unconditional Mertens logarithmic error is smaller than the inverse square logarithm.",
        H("Strengthened Mertens error"),
        Blocks(Describe.Lean(
            DescribeId.Create("strengthened-mertens"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/Mertens.strengthened_mertens"),
            H("Inverse-square logarithmic error"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For the original inclusive Mertens error E3, positive constants c and C give abs(E3(x))<=C exp(-c(log(x))^(1/10)) for all sufficiently large x. Consequently E3(x)=o(1/log(x)^2). The Euler constant and all prime-power endpoints are retained exactly. No Riemann hypothesis or supplied stronger Mertens estimate is assumed.")),
                Paragraph(Text("The existing unconditional weighted Mangoldt rate bounds E1Lambda(x)+gamma by a stretched exponential. Substitution into the exact E2Lambda identity cancels the constant term and bounds both the endpoint and complete integral by the same rate divided by log(x). The exact complete Mangoldt identity expresses E3 as minus E2Lambda minus the omitted prime-power residual. Each residual is bounded by its corresponding omitted lcm Euler logarithm, whose existing total bound is 4/sqrt(x). Both errors vanish after multiplication by log(x)^2."))),
            DescribeRole.Theorem))));
}
