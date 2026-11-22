using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class SpectralDeterminantReflectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/SpectralDeterminantReflection";
    private const string Title = "Soundness of the polynomial determinant certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("spectraldeterminantreflection-crosscheck-sound"),
                DeclarationHandle.Create(Module + ".crossCheck_sound"),
                H("Soundness of the polynomial determinant certificate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite cross-multiplication check establishes the corresponding polynomial matrix identity."))),
                DescribeRole.Theorem))));
}
