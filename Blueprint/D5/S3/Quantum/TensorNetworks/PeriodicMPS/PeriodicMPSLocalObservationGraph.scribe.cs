using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSLocalObservationGraphDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSLocalObservationGraph";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local observation graphs and their normal jets",
        H("Local observation graphs and their normal jets"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpslocalobservationgraph-result"),
            DeclarationHandle.Create(Module + ".normal_graph_remainder"),
            H("Local observation graphs and their normal jets"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The inverse function theorem and a remainder estimate transport the normal Taylor expansion to the analytic observation graph."))),
            DescribeRole.Theorem))));
}
