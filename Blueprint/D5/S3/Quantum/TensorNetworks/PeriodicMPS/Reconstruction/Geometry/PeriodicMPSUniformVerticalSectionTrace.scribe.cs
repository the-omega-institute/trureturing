using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformVerticalSectionTraceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSectionTrace";
    private const string Title = "Trace and transverse identities on the paired section";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformverticalsectiontrace"),
                DeclarationHandle.Create(Module + ".transverse_singlet_eq"),
                H("Transverse derivative of the singlet readout"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The transverse singlet derivative at length 2 + n is the bra commutator determinant times the nth coefficient of the complete series."))),
                DescribeRole.Theorem))));
}
