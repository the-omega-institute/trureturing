using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;
internal sealed class LatticeBcGhostCohomologyJacobiDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full signed coefficient Jacobi on the original BRST quotient.",
        H("Finite coefficient sums"),
        Blocks(
            Paragraph(Text("Every operation is the bilinear quotient product constructed from the actual tensor Y and unchanged original Q. The previously proved unrestricted tensor Borcherds theorem is reused, not recredited as a new proof.")),
            Describe.Lean(DescribeId.Create("left-finite"), DeclarationHandle.Create(Prefix + "leftTerm_finite"), H("Finite left coefficient support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Finite support survives passage from actual cycle products to quotient products."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-finite"), DeclarationHandle.Create(Prefix + "rightTerm_finite"), H("Finite signed right coefficient support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The complete signed right coefficient sums are finite at every integer parameter."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("homogeneous-jacobi"), DeclarationHandle.Create(Prefix + "borcherds"), H("All integer homogeneous signed Jacobi"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A quotient class fixed by a parity projection is represented by applying that actual projection to any closed representative. The prior odd-Q proof ensures this projected representative remains closed; no unsupported homogeneous-representative assumption is made."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mixed-jacobi"), DeclarationHandle.Create(Prefix + "mixed_borcherds"), H("Explicit four-component mixed identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The quotient identity includes all four even/odd components, with the actual Koszul signs and all integer mode parameters. Projection, finite sums, and quotient maps are linked by proved equalities."))), DescribeRole.Theorem))));
}
