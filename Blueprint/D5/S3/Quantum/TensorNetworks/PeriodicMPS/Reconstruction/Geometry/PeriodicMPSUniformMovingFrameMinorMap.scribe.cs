using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformMovingFrameMinorMapDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameMinorMap";
    private const string Title = "Scalar extension of section minors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformmovingframeminormap"),
                DeclarationHandle.Create(Module + ".sectionTripletMinor_map"),
                H("Change of scalars for the triplet minor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mapping the entries through a complex algebra homomorphism agrees with evaluating the triplet minor at the mapped section parameters."))),
                DescribeRole.Theorem))));
}
