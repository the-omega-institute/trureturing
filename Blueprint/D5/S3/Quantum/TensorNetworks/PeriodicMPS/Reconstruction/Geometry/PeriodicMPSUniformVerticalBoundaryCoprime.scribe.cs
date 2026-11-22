using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformVerticalBoundaryCoprimeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalBoundaryCoprime";
    private const string Title = "Boundary coprimality of the divided outer determinant";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformverticalboundarycoprime"),
                DeclarationHandle.Create(Module + ".hsymm_isRelPrime_outerDividedDet"),
                H("Outer determinant and complete homogeneous equation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over the characteristic-zero coefficient field and for m at least three, the complete homogeneous polynomial of degree m − 2 is relatively prime to the divided outer determinant."))),
                DescribeRole.Theorem))));
}
