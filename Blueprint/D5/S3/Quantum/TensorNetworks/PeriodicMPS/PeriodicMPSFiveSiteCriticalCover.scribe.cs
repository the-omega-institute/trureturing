using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteCriticalCoverDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteCriticalCover";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five-site critical equations in real coordinates",
        H("The five-site critical equations in real coordinates"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitecriticalcover-result"),
            DeclarationHandle.Create(Module + ".cover_critical_equations"),
            H("The five-site critical equations in real coordinates"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Countably many differentiable images of six real variables cover the physical common zeros of the two minors."))),
            DescribeRole.Theorem))));
}
