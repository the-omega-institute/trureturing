using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformMovingFrameFactorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameFactor";
    private const string Title = "Matrix factorization through the native frame";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformmovingframefactor"),
                DeclarationHandle.Create(Module + ".sectionColumns_factor"),
                H("Factorization for swap-symmetric columns"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the observed coordinates of swap-symmetric section columns lie in the image of the native matrix, every matrix obtained by applying linear row functionals to those columns factors through the native matrix."))),
                DescribeRole.Theorem))));
}
