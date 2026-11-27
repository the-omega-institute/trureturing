using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class ChirpedActualSeedBoundsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedActualSeedBounds";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact order-73 correlation system has a certified zero.",
        H("Root certification in order 73"),
        Blocks(
            Describe.Lean(DescribeId.Create("exists-unique-zero-closed-ball"),
                DeclarationHandle.Create(Module + ".existsUnique_zero_closedBall"),
                H("Unique zero in the order-73 certificate ball"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integer sums use the same spectral orbit data and dyadic center as the exact residual. The "
                    + "seed values and slopes obey the signed fixed-point error bounds. These bounds, the exact "
                    + "Jacobian identification and the operator norm drift estimate close the hypotheses of the "
                    + "preconditioned root certificate."))),
                DescribeRole.Theorem))));
}
