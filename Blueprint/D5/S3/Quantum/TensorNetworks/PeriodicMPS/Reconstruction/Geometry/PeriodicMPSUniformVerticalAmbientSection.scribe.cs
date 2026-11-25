using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformVerticalAmbientSectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalAmbientSection";
    private const string Title = "Coordinate guards for vertical sections";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformverticalambientsection"),
                DeclarationHandle.Create(Module + ".genericSection_coordinate_guards"),
                H("Guard nonvanishing on an admissible pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nondivisibility by the pairing obstruction ensures that the two paired sums, their difference, and the balanced mixed-transfer expression are nonzero in the generic section field."))),
                DescribeRole.Theorem))));
}
