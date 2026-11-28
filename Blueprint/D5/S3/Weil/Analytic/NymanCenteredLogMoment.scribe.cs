using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanCenteredLogMomentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Analytic/NymanCenteredLogMoment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first logarithmic moment of centered prime dilations",
        H("The first logarithmic moment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nyman-centered-first-logarithmic-moment"),
                DeclarationHandle.Create(Module + "integral_centeredPrime_log_weighted"),
                H("The exact first logarithmic moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral of the centered prime sum times log x divided by x squared "
                    + "equals the ordinary kernel moment times twice the Euler–Mascheroni "
                    + "constant plus the higher prime power series at one minus one. "
                    + "The pole terms from the zeta function and its logarithmic derivative "
                    + "cancel in the centered Dirichlet series. Absolute integrability with "
                    + "the extra logarithm permits passage to the right difference quotient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nyman-centered-first-logarithmic-moment-positive"),
                DeclarationHandle.Create(Module + "integral_centeredPrime_log_weighted_pos"),
                H("Strict positivity of the moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fixed kernel moment is positive. The higher prime power series "
                    + "is nonnegative, and the Euler–Mascheroni constant exceeds one half."))),
                DescribeRole.Theorem))));
}
