using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSImmersionPullbackDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSImmersionPullback";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pullback of small observation sets",
        H("Pullback of small observation sets"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsimmersionpullback-result"),
            DeclarationHandle.Create(Module + ".cover_regular_preimage"),
            H("Pullback of small observation sets"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The regular preimage of a countable differentiable cover has a countable differentiable cover with the same parameter dimension."))),
            DescribeRole.Theorem))));
}
