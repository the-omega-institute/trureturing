using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class ChirpedAnalyticReplayBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticReplayBridge";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identification of analytic residuals and Jacobians with replay rows.",
        H("Identification of analytic residuals and Jacobians with replay rows"),
        Blocks(
            Describe.Lean(DescribeId.Create("residual-eq"),
                DeclarationHandle.Create(Module + ".residual_eq"),
                H("The analytic residual equals the exact replay residual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For valid left and right seed layouts in each row, the modular permutation and the replay index "
                    + "have the same action when the unit represents the supplied inverse. The residual sums agree "
                    + "under the common real or imaginary projection."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jacobian-eq"),
                DeclarationHandle.Create(Module + ".jacobian_eq"),
                H("The analytic derivative matrix equals the exact replay Jacobian"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same layout and inverse hypotheses, evaluation on a coordinate basis vector "
                    + "identifies each derivative entry with the sum of the two seed slope terms in the replay."))),
                DescribeRole.Theorem))));
}
