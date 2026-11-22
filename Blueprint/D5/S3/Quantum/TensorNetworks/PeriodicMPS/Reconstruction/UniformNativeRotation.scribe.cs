using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class UniformNativeRotationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformNativeRotation";
    private const string Title = "Physical rotation columns of the native critical matrix";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("uniformnativerotation"),
                DeclarationHandle.Create(Module + ".fderiv_rawReadout_rotationColumn"),
                H("Polynomial evaluation of a rotation column"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rotation columns of the raw readout derivative are the real parts of the evaluated rotation polynomials."))),
                DescribeRole.Theorem))));
}
