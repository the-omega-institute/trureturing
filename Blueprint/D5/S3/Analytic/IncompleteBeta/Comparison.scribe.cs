using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.IncompleteBeta;

internal sealed class ComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict concentration comparison for symmetric beta means.",
        H("Beta means and shape imbalance"), Blocks(
            Describe.Lean(DescribeId.Create("incomplete-beta-mean-imbalance"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta/Comparison.betaMean_strictAntiOn"),
                H("Strict decrease with imbalance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let W be a real continuous function on the closed unit interval, invariant under reflection about its midpoint, and strictly increasing on the interval from zero, excluded, to one half, included. For m positive, its normalized beta mean with shapes m+d and m-d is strictly decreasing for d from zero, included, to m, excluded. The normalization is the beta integral, equivalently the product of the two shape Gamma values divided by Gamma(2m).")),
                    Paragraph(Text("Reflection folds both the moment and the normalizing integral onto the left half of the unit interval. There the density is twice [u(1-u)] to the power m-1 times cosh(d log((1-u)/u)). For two ordered nonnegative imbalances, the ratio of the larger tilt to the smaller tilt strictly decreases with u. An iterated integral of the product of the differences in W and in the weighted densities is positive. Its algebraic expansion yields twice the difference between the cross-multiplied moments. The beta density is the fractional weight with parameters 1-m+d and 2m-1. Its integrability and Gamma-valued integral supply the endpoint control and normalization, while continuity of W ensures integrability of each moment."))),
                DescribeRole.Theorem))));
}
