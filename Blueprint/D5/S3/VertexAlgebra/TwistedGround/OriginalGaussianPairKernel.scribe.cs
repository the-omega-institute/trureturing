using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianPairKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original elementary pair kernel", H("Original elementary pair kernel"), Blocks(
            Paragraph(Text("The scalar power-series kernel is defined independently as 1/(2 sqrt(1+a) sqrt(1+b) (sqrt(1+a)+sqrt(1+b))^2), with the constant-one formal binomial roots and native multivariate inverse. The original halfBinomial and pairScalar definitions are reused unchanged from LatticeHalfFockFiniteCorrection.")),
            Paragraph(Text("The comparison series has coefficient pairScalar(m+1,n+1). Both series satisfy the same equation after multiplication by (a-b)^2. The proof checks the scalar second difference, the origin and both axes, and cancels the nonzero polynomial in the formal power-series domain. Every natural m,n is included; no diagonal exclusion or desired kernel equality is assumed.")),
            Paragraph(Text("The mathematical source was adapted and API-corrected from the two hash-pinned completed supplier sources collected on 2026-11-02. This is a formal scalar coefficient correspondence. It does not identify raw T, U, coloured G or the original infinite M with an analytic sewn-curve bidifferential, and establishes no full Jacobi, no-ghost, string or AdS/CFT completion.")),
            Paragraph(Text("Audit limitation under CLAUDE 3.9: the faithful Reg mirror for D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPairKernel.kernel_coeff compiles, but the current scoped report records declared_unresolved, certificate=null, IE-C050 ClosedTruthReadout, reason=unclassified_form, rule=source.residual_requires_open, with escape_continues.kind=open. The unfinished template assessment is disclosed against the existing issue https://github.com/the-omega-institute/trureturing/issues/5214. No declared_validated audit, admission or freeze is claimed; the judge is unchanged.")),
            Describe.Lean(DescribeId.Create("kernel"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPairKernel.kernel"),
                H("kernel"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The independent elementary root/inverse kernel."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kernel-coeff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPairKernel.kernel_coeff"),
                H("kernel_coeff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All coefficients are the unchanged original Corr pair scalars."))), DescribeRole.Theorem))));
}
