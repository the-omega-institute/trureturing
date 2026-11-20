using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteLocalGraphsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteLocalGraphs";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four certified local observation graphs",
        H("Four certified local observation graphs"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitelocalgraphs-result"),
            DeclarationHandle.Create(Module + ".exists_certified_graph"),
            H("Four certified local observation graphs"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The raw five-site observation has an analytic graph at each of the four special lifts, with an exact normal cubic coefficient."))),
            DescribeRole.Theorem))));
}
