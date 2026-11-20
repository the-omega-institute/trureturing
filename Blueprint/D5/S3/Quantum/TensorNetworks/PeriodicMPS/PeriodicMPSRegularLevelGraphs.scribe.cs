using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSRegularLevelGraphsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSRegularLevelGraphs";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Graph covers for regular level sets",
        H("Graph covers for regular level sets"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsregularlevelgraphs-result"),
            DeclarationHandle.Create(Module + ".countable_cover_regular_level"),
            H("Graph covers for regular level sets"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "At a regular level where the last derivative is nonzero, countably many differentiable graphs cover the level set."))),
            DescribeRole.Theorem))));
}
