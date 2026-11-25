using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSCommonSpectralJetsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSCommonSpectralJets";
    private const string Title = "The literal trace-word Jacobian";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpscommonspectraljets-literaljacobian-eq-closedform"),
                DeclarationHandle.Create(Module + ".literalJacobian_eq_closedForm"),
                H("The literal trace-word Jacobian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A recurrence for the common spectral witness gives the closed form of its nine-by-nine trace-word Jacobian."))),
                DescribeRole.Theorem))));
}
