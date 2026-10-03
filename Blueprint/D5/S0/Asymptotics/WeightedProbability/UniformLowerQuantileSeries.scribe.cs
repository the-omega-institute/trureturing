using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class UniformLowerQuantileSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var index = F.Id("j");
        var sample = F.Id("x");
        var scale = F.Id("c");
        var error = Delta;
        var values = Seq(F.Id("X"), Underscore, Grp(index));
        var weight = Seq(F.Id("w"), Underscore, Grp(index));
        var weighted = Seq(scale, Sp, weight);
        var total = Seq(Sum, Underscore, Grp(index), Sp, values, Open, sample, Close);
        var weightSum = Seq(Sum, Underscore, Grp(index), Sp, weight);
        var lowerSet = Call("set", sample, Seq(values, Open, sample, Close, Lt, weighted));
        var finiteSet = Call("set", sample, Seq(total, Neq, Infty));
        var quantiles = Seq(
            Forall, Sp, error, Gt, D(0), Comma, Sp,
            Exists, Sp, scale, Gt, D(0), Comma, Sp,
            Forall, Sp, index, Comma, Sp,
            Mu, Open, lowerSet, Close, Leq, error);

        return DocumentDefinition.Create(ScribeNode.Create(
            "A finite measure and arbitrarily reliable uniform lower quantiles force a nonnegative series to diverge almost everywhere, without independence.",
            H("Uniform Lower Quantile Series"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("uniform-lower-quantiles-force-almost-everywhere-divergence"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/UniformLowerQuantileSeries."
                        + "ae_tsum_eq_top_of_uniform_lower_quantiles"),
                    H("Almost-everywhere divergence from marginal lower quantiles"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("FiniteMeasure", Mu), Sp, Land, Sp,
                        Open, Forall, Sp, index, Comma, Sp, Call("Measurable", values), Close,
                        Sp, Land, Sp, weightSum, Eq, Infty,
                        Sp, Land, Sp, Open, quantiles, Close,
                        Sp, Rightarrow, Sp, Mu, Open, finiteSet, Close, Eq, D(0)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The weights and measurable variables are nonnegative extended real numbers. Error and scale are finite positive real numbers. For each error one scale works for every index, rather than a different scale for each index.")),
                        Paragraph(Text(
                            "Restricting to a positive-measure event with bounded total determines the error as half its measure. Every restricted summand then has a uniform integral lower bound. Tonelli's theorem contradicts the finite integral of the bounded total.")),
                        Paragraph(Text(
                            "For an absolute discrepancy with uniform quadratic-scale marginal tightness, the reciprocal square-root logarithmic profile has these lower quantiles against the divergent weights one divided by (j+1) log(j+2). A predictable hazard bounded below by that profile consequently has almost-sure accumulated divergence."))),
                    DescribeRole.Theorem)),
            []));
    }
}
