using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class GaussianExternalBlockDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "GaussianExternalBlock", H("GaussianExternalBlock"), Blocks(
            Paragraph(Text("Finite external coordinates and square-summable mixed rows define bounded bilinear Gaussian block operators. A positive external scale makes the joint operator a strict Hilbert-Schmidt contraction.")),
            N("bilinear_eq_tsum","Actual bilinear coordinate functional","The bounded complex-linear functional is inner(star r,z). The coordinate conjugation cancels the conjugate-linear first slot of the Hilbert inner product, giving sum_i r_i z_i. Analytic estimates may use Hilbert inner products, but the sewing contraction has no coordinate conjugation."),
            N("operator_entry","A genuine scaled joint operator","Extend A to the internal summand by the orthogonal coordinate inclusion and its adjoint. Add the actual finite sum of bilinear rank-one mixed terms and the external rank-one matrix. The resulting bounded operator polynomial has entries [[t^2 P,tR],[tR^t,A]]. No Gaussian coefficient or norm conclusion is stored as data."),
            N("exists_positive_scale","A positive external scale","At t=0 the actual bounded joint operator is just the orthogonal extension of A, whose norm is strictly less than one. Continuity of the operator polynomial and of its norm yields a positive real t for which the full scaled joint operator is a strict contraction. This imposes no restriction on the original finite P or mixed l2 rows."),
            N("operator_square_summable","The two mixed rectangles","The external rectangle is finite. Each mixed rectangle has a finite family of actual square-summable rows or columns. The remaining rectangle is the given Hilbert-Schmidt matrix of A. Splitting the product index into four disjoint rectangles proves the true full matrix square sum is finite.")), []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("gaussianexternalblock-" + name.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
