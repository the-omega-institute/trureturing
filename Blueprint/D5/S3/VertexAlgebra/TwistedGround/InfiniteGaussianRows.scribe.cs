using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class InfiniteGaussianRowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "InfiniteGaussianRows", H("InfiniteGaussianRows"), Blocks(
            Paragraph(Text("Fixing an external occupation selects a square-summable slice of the joint factorial Gaussian norm. Pairing two such slices gives an absolutely convergent internal contraction.")),
            N("row_square_summable","Every fixed external row is in factorial l2","Apply the existing InfiniteGaussianFock.Data.occupation_summable theorem to the actual scaled joint block. Restrict the nonnegative joint sum to the injection n maps to (d,n). Its factorial weight is d!n!, and exact diagonal congruence contributes abs(t^degree(d))^2. Both external factors are strictly positive, so cancelling them proves sum_n n! abs(c_K(d,n))^2 is finite. The scale can be chosen independently for each block because the resulting row estimate concerns the original unscaled coefficients."),
            N("contraction_norm_summable","Absolute internal sewing convergence","For every pair of finite external occupations, use the two actual row square sums and the inequality ab <= (a^2+b^2)/2. This proves summability of abs(n! c_K1(d,n)c_K2(n,e)). No positivity, commutation, nonzero normalization, full joint smallness or supplied convergence hypothesis is required."),
            N("cutoff_tendsto","The whole coordinate support net","For F ranging over all finite internal coordinate sets, retain all occupations supported in F, with no degree cutoff. Every fixed occupation is eventually retained, and the proved absolute series dominates every cutoff. Dominated convergence identifies the cutoff limit with the whole native contraction. Empty internal and external types are retained.")), []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("infinitegaussianrows-" + name.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
