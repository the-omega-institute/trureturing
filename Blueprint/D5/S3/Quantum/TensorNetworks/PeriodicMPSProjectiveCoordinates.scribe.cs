using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSProjectiveCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSProjectiveCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projective coordinates for complex amplitudes",
        H("Projective coordinates for complex amplitudes"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsprojectivecoordinates-result"),
            DeclarationHandle.Create(Module + ".eq_smul_of_projector_eq"),
            H("Projective coordinates for complex amplitudes"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Equality of normalized rank-one projectors gives equality of nonzero amplitudes up to a nonzero scalar."))),
            DescribeRole.Theorem))));
}
