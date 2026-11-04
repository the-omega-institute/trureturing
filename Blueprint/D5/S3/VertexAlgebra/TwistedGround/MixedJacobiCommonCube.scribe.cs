using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class MixedJacobiCommonCubeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual signed Jacobi common-cube contraction",
        H("Actual signed Jacobi common-cube contraction"),
        Blocks(
            Paragraph(Text("The complete second-input outer branch first bounds z by actual original-source nilpotence, gathers ell,z at L and reorders the resulting finite sums. Its external (-1)^r makes its phase C=(-1)^(n+1-p-H+q+d)/(p!q!L!). The first-input phase is -C(-1)^R, where R=2d-L-m-r-2. Input lowering bounds p<K-1 and q<H-1, original source nilpotence, and the two actual ordered-product weight bounds permit padding to one common finite cube before the contractions are combined.")),
            Describe.Lean(DescribeId.Create("mixed-homogeneous-grade-pairing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedJacobiCommonCube.mixed_homogeneous_grade_pairing"),
                H("The common-cube identity on the entire target grade"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual input-lowering bounds, original source nilpotence and both ordered-product support conditions provide one finite p,q,L cube. The first-input phase is -C(-1)^R and the second-input phase is C. The all-source supplier cancels both ordered products. mixed_residual_homogeneous consumes this equality on every target-grade vector, before the separate off-grade calculation and all-vector extension."))), DescribeRole.Theorem))));
}
