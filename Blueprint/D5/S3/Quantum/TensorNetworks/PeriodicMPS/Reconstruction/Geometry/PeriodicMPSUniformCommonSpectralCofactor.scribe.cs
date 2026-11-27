using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformCommonSpectralCofactorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralCofactor";
    private const string Title = "An exact native cofactor is nonzero";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformcommonspectralcofactor-nativewitness-exists-cofactor-ne-zero"),
                DeclarationHandle.Create(Module + ".nativeWitness_exists_cofactor_ne_zero"),
                H("An exact native cofactor is nonzero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal witness gives rank nine for the native matrix and hence a nonzero maximal minor."))),
                DescribeRole.Theorem))));
}
