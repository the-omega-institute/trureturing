using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class MaximalRealPartProjectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Laplace/MaximalRealPartProjection.";

    private static DocumentBlock.Describe Entry(string id, string name, string title, string statement,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An absolutely summable exponential series projects asymptotically onto its maximal real-part line.",
        H("Maximal real-part projection"),
        Blocks(
            Paragraph(Text("Let a and z be complex sequences indexed by ℕ and let Θ and t be real. "
                + "Write P(t) for the sum over indices with Re(z(n))=Θ. The other terms decay after normalization.")),
            Entry("maximal-series", "maximalSeries", "Series on the maximal real-part line",
                "P(t) is the sum of the maximal terms over ℕ.", DescribeRole.Definition),
            Entry("uniform-continuous-maximal-series", "uniformContinuous_maximalSeries",
                "Uniform continuity of the projection",
                "With summable coefficient norms, P is uniformly continuous as a uniform limit of "
                + "uniformly continuous finite Fourier sums.", DescribeRole.Theorem),
            Entry("tendsto-exp-mul-tsum-sub-maximal-series", "tendsto_exp_mul_tsum_sub_maximalSeries",
                "Projection of the externally normalized sum",
                "If the coefficient norms are summable and Re(z(n))≤Θ for all n, then "
                + "exp(−Θt) ∑ₙ a(n) exp(t z(n))−P(t) tends to zero as t tends to +∞.",
                DescribeRole.Theorem))));
}
