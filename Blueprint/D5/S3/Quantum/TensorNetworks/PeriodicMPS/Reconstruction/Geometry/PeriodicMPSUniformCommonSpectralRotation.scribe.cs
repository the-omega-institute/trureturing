using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformCommonSpectralRotationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralRotation";
    private const string Title = "Rotation columns at the witness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformcommonspectralrotation-eval-rotationpolynomial-eq-invariant"),
                DeclarationHandle.Create(Module + ".eval_rotationPolynomial_eq_invariant"),
                H("Rotation columns at the witness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluating the rotation polynomials gives the corresponding derivatives of the invariant Gram entries."))),
                DescribeRole.Theorem))));
}
