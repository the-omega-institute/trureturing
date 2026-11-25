using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformCommonSpectralGenericDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralGeneric";
    private const string Title = "A cofactor survives both specializations";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformcommonspectralgeneric-determinantchart-exists-generic-cofactor-ne-zero"),
                DeclarationHandle.Create(Module + ".determinantChart_exists_generic_cofactor_ne_zero"),
                H("A cofactor survives both specializations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At each required length a single native cofactor index gives a nonzero element in both generic special charts."))),
                DescribeRole.Theorem))));
}
