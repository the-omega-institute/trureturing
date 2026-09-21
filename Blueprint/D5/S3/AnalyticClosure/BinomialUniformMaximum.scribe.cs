using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class BinomialUniformMaximumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sharp Gaussian upper bound holds uniformly over all binomial indices.",
        H("Uniform Binomial Upper Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("binomial-uniform-gaussian-upper-bound"),
            DeclarationHandle.Create(
                "D5/S3/AnalyticClosure/BinomialUniformMaximum.uniform_upper"),
            H("Uniform upper bound without a mode assumption"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every real parameter p strictly between zero and one and every "
                + "positive epsilon, all sufficiently large n satisfy "
                + "binomialMass(p,n,k) sqrt(2 pi n p (1-p)) <= 1+epsilon "
                + "at every k from zero through n. The proof combines the "
                + "existing relative local Gaussian approximation with its scaled "
                + "tail estimate. It assumes no formula for the maximizing index."))),
            DescribeRole.Theorem))));
}
