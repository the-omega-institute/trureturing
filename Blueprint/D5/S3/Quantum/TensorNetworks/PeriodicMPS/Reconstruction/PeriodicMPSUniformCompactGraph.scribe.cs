using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformCompactGraphDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformCompactGraph";
    private const string Title = "The compact graph of periodic bond-two projectors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformcompactgraph-result"),
            DeclarationHandle.Create(Module + ".source_isCompact"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every positive period the closure of the graph pairing weighted invariant projectors with actual trace-word projectors is compact. The second projection maps this graph onto the closure of the actual projector image."))),
            DescribeRole.Theorem))));
}
