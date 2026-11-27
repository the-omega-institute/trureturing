using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomerySublogZeroLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/MontgomerySublogZeroLimit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zero-frequency pair sum attains the leading coefficient under sublogarithmic counting error.",
        H("The zero-frequency limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tendsto-pair-sum-zero-of-sublog-discrepancy"),
                DeclarationHandle.Create(Owner + ".tendsto_pairSum_zero_of_sublog_discrepancy"),
                H("The exact zero-frequency coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write c = 1/(2π). Assume the inclusive count differs from cY(log(cY)−1) by o(log Y). The ordered Lorentz pair sum at zero, divided by Y(log Y)², tends to 2πc².")),
                    Paragraph(Text("At zero frequency every difference cosine equals one. The alignment lower bound and the uniform upper bound therefore approach the same coefficient from both sides."))),
                DescribeRole.Theorem))));
}
