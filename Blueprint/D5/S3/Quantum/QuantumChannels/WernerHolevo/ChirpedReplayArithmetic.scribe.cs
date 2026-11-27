using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class ChirpedReplayArithmeticDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplayArithmetic";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed fixed-point error bounds for the replay.",
        H("Signed fixed-point error bounds for the replay"),
        Blocks(
            Describe.Lean(DescribeId.Create("root-error"),
                DeclarationHandle.Create(Module + ".root_error"),
                H("Uniform error for computed roots of unity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each frequency index in the cyclic order, the error after decoding is at most 45 divided by "
                    + "the fixed scale. The bound propagates the Taylor and signed-rounding errors through three "
                    + "rounded squarings."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cayley-error"),
                DeclarationHandle.Create(Module + ".cayley_error"),
                H("Signed rational bounds for phases and slopes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A rational input with positive denominator gives fixed-point approximants to the Cayley phase "
                    + "and its slope. Each decoded approximation has error at most two divided by the fixed scale."))),
                DescribeRole.Theorem))));
}
