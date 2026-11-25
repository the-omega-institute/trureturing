using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformCommonSpectralSliceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralSlice";
    private const string Title = "Native slice derivative at the witness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformcommonspectralslice-eval-pderiv-rawslicepolynomial"),
                DeclarationHandle.Create(Module + ".eval_pderiv_rawSlicePolynomial"),
                H("Native slice derivative at the witness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Formal partial differentiation of a native raw-slice entry agrees with its literal trace-word derivative at the balanced witness."))),
                DescribeRole.Theorem))));
}
