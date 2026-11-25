using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformVerticalSectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSection";
    private const string Title = "Weighted and boundary formulas for the outer section";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformverticalsection"),
                DeclarationHandle.Create(Module + ".outerDividedDet_boundary"),
                H("Boundary value of the divided determinant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With the second root of each pair set to zero, the divided outer determinant is −8(m + 2)²(xy)^(3m + 4) z(z − 1)² for m at least three."))),
                DescribeRole.Theorem))));
}
