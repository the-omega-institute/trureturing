using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSCompactFiberDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSCompactFiber";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Descent through compact fibers",
        H("Descent through compact fibers"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpscompactfiber-result"),
            DeclarationHandle.Create(Module + ".descend_open_dense"),
            H("Descent through compact fibers"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "A compact closed map carries openness and density to the set of values whose full fibers lie in a dense open set, when the relevant fibers are singletons."))),
            DescribeRole.Theorem))));
}
