using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KummerRatio;

internal sealed class BetaAsymptoticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gamma limits for exponentially weighted beta integrals.",
        H("Beta integral endpoint asymptotics"), Blocks(
            Describe.Lean(DescribeId.Create("beta-laplace-endpoint"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/BetaAsymptotics.tendsto_beta_laplace"),
                H("Exponential concentration at the endpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive real parameters s and d, multiply the integral from zero to one of exp(xt) times t to the power s-1 times (1-t) to the power d-1 by exp(-x) times x to the power d. The resulting quantity tends to Gamma(d) as x tends to positive infinity.")),
                    Paragraph(Text("The normalized Gamma density gives an approximate identity on the real line. Reflecting the integration variable places the concentration point at zero. The remaining endpoint weight is integrable for every positive s and continuous at zero, including when its other endpoint is singular. The approximate identity theorem therefore supplies the limit without a boundedness assumption at that endpoint."))),
                DescribeRole.Theorem))));
}
