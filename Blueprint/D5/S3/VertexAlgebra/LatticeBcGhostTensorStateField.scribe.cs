using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;
internal sealed class LatticeBcGhostTensorStateFieldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual lattice matter tensor bc state-field on the original carrier.",
        H("Compiled bridges"),
        Blocks(
            Paragraph(Text("TensorProduct.lift composes the accepted finite integer-mode convolution with the actual lattice and bc state fields. The matter factor is even; parity is carried by the bc factor.")),
            Describe.Lean(DescribeId.Create("creation"), DeclarationHandle.Create(Prefix + "stateField_creation"), H("All-state creation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Creation is proved on arbitrary algebraic tensor states by tensor induction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("creativity"), DeclarationHandle.Create(Prefix + "stateField_creativity"), H("Vacuum creativity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every nonnegative mode vanishes on the actual tensor vacuum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parity"), DeclarationHandle.Create(Prefix + "parity_decomposition"), H("Actual parity decomposition"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The second-factor parity projections are idempotent, orthogonal, and exhaustive on arbitrary tensor states."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("translation"), DeclarationHandle.Create(Prefix + "translation_original"), H("Original translation bridge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The bridge retains both Gram inverse equations."))), DescribeRole.Theorem))));
}
