using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteCompactGraphDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactGraph";
    private const string Title = "The ordinary chart of the compact seven-site trace graph";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitecompactgraph-result"),
            DeclarationHandle.Create(Module + ".image_traceChart"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The compact trace graph pairs the projector of the six weighted invariant coordinates with the full seven-site trace-word projector. Its ordinary part is exactly the image of the four complex coordinates obtained by fixing the first trace to one and requiring a nonzero amplitude.")),
                Paragraph(Text("A nonzero first diagonal entry of the weighted projector lets the decoder recover the normalized trace coordinates. At a defined amplitude, the graph limit above the corresponding weighted projector is unique. The ordinary part is open, dense and path connected in the compact graph."))),
            DescribeRole.Theorem))));
}
