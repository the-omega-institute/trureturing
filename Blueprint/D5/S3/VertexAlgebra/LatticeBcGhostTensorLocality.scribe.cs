using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;
internal sealed class LatticeBcGhostTensorLocalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeBcGhostTensorLocality.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed locality for actual lattice matter tensor bc fields.",
        H("Compiled locality"),
        Blocks(
            Paragraph(Text("The matter sign is one and the bc sign is koszul. Factor locality is transferred through finite convolution and then extended over the homogeneous ranges and the mixed four-component expansion.")),
            Describe.Lean(DescribeId.Create("homogeneous"), DeclarationHandle.Create(Prefix + "homogeneous_superLocal"), H("Homogeneous signed locality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The statement applies to arbitrary states in the actual homogeneous carrier ranges."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mixed"), DeclarationHandle.Create(Prefix + "mixed_locality"), H("Mixed parity locality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The common clearing order handles all four parity components."))), DescribeRole.Theorem))));
}
