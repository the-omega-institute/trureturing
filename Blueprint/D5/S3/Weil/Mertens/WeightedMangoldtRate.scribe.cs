using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;
internal sealed class WeightedMangoldtRateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Retained arithmetic suppliers consumed by the full actual-K source attempt.",
        H("Reuse-only weighted Mangoldt suppliers"), Blocks(
            Describe.Lean(DescribeId.Create("chebyshev-tail-bound"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/WeightedMangoldtRate.chebyshev_tail_bound"),
                H("Complete Chebyshev tail bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive c, nonnegative D, X>=2 and x>=X, an actual psi error bound D u exp(-2c(log u)^(1/10)) bounds the complete tail integral by D times the full positive weight mass times exp(-c(log x)^(1/10)). The retained proof body is unchanged. This visibility export is consumed to obtain the exact original B in the full certificate; it is not a standalone content request."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("e1lambda-stretched-exponential"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/WeightedMangoldtRate.E1Lambda_stretched_exponential"),
                H("Retained inclusive Mangoldt rate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The retained unconditional theorem gives positive c,C and X>=2 with abs(E1Lambda(x)+gamma)<=C exp(-c(log x)^(1/10)) for every x>=X. It includes every prime power and equality at cutoffs. Its earlier evidence remains separately scoped. This payload reuses its arithmetic suppliers and does not seek standalone readmission of this theorem or claim a new compilation."))),
                DescribeRole.Theorem))));
}
