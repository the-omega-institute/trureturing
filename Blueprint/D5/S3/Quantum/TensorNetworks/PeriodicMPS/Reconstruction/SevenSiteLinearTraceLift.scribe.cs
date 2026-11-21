using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteLinearTraceLiftDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLinearTraceLift";
    private const string Title = "Recovering the weighted trace lift from the full seven-site projector";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitelineartracelift-result"),
            DeclarationHandle.Create(Module + ".lift_eq_of_readColumn_ne_zero"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Apply six fixed seven-letter trace contrasts to a column of the full state projector. On ordinary trace amplitudes these contrasts give one common multiple of the six weighted trace coordinates.")),
                Paragraph(Text("At a point of the compact graph, if the first component of the resulting vector is nonzero, its projector is the weighted trace projector in the graph. The identity passes to graph limits by continuity. In this region the full state projector has a unique graph lift."))),
            DescribeRole.Theorem))));
}
