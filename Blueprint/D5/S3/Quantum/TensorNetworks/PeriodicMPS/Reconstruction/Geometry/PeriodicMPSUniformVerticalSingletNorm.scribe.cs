using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformVerticalSingletNormDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSingletNorm";
    private const string Title = "Coprimality of the singlet and middle expressions";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformverticalsingletnorm"),
                DeclarationHandle.Create(Module + ".hsymm_isRelPrime_literalMiddle"),
                H("No common factor for the literal middle expression"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For m at least four, the complete homogeneous equation and the literal middle factor on the section are relatively prime."))),
                DescribeRole.Theorem))));
}
