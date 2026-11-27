using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSMonicLevelGraphsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSMonicLevelGraphs";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Graph covers for monic polynomial levels",
        H("Graph covers for monic polynomial levels"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsmoniclevelgraphs-result"),
            DeclarationHandle.Create(Module + ".countable_cover_monic_level"),
            H("Graph covers for monic polynomial levels"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The zero set of a monic real polynomial with polynomially varying coefficients is covered by countably many differentiable graphs."))),
            DescribeRole.Theorem))));
}
