using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RobinActualWeightedTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/IntegratedExplicit/RobinActualWeightedTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute logarithmic tail transport.",
        H("Absolute logarithmic tail transport"),
        Blocks(
            Paragraph(Text("The weight A is the product of the exponential factor and the inverse-log coefficient. Its negative derivative d is nonnegative and has tail mass A at every positive endpoint.")),
            Describe.Lean(DescribeId.Create("transport"), DeclarationHandle.Create(Prefix + "logarithmic_transport"),
                H("Weighted integral transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real j at least 1 and a positive endpoint u, absolute Fubini on the ordered triangle transports any integrable K on (u,∞). The result includes integrability of both weighted expressions and the boundary term minus the integral of d against the tail of K."))), DescribeRole.Theorem)
        )));
}
