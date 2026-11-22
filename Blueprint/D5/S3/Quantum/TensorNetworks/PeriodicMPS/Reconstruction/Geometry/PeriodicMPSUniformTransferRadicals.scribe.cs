using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformTransferRadicalsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferRadicals";
    private const string Title = "Split coordinates and their transfer radicals";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformtransferradicals"),
                DeclarationHandle.Create(Module + ".coordinateEquivRadical"),
                H("Equivalence of coordinate and radical fibers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With two, U, and k nonzero, the split coordinate fiber is equivalent to the two-root radical fiber."))),
                DescribeRole.Definition))));
}
