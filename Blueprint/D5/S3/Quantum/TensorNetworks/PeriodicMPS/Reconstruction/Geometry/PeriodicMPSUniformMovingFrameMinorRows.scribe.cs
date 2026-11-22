using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformMovingFrameMinorRowsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameMinorRows";
    private const string Title = "Triplet and singlet rows in the moving frame";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformmovingframeminorrows"),
                DeclarationHandle.Create(Module + ".tripletContractRow"),
                H("Triplet row contraction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This row evaluates one of the triplet coordinates of a raw two-site matrix. The same contractions are used to express the triplet section minor in native coordinates."))),
                DescribeRole.Definition))));
}
