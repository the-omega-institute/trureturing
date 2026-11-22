using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformTernaryRemainderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTernaryRemainder";
    private const string Title = "Ternary norm identity on the homogeneous zero locus";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformternaryremainder"),
                DeclarationHandle.Create(Module + ".ternaryNorm_of_h_zero"),
                H("Ternary middle expression on the zero locus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Where the complete homogeneous expression of degree k + 2 vanishes, the ternary middle expression times the square of the root product equals the root product to the power k + 4."))),
                DescribeRole.Theorem))));
}
