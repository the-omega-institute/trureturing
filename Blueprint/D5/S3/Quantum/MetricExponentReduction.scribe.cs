using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class MetricExponentReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/MetricExponentReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An inverse-linear metric weight lowers a quadratic small-spacing density to an "
            + "exactly linear asymptotic law.",
        H("Metric Exponent Reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("inverse-metric-reduces-quadratic-exponent"),
                DeclarationHandle.Create(Prefix + "inverse_metric_reduces_quadratic_exponent"),
                H("Inverse metric weight lowers exponent two to one"),
                StatementSource.FromAuthor(ReductionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the positive-side filter, assume lambda times the metric weight tends "
                            + "to m>0 and the density divided by lambda squared tends to c>0. "
                            + "Their product is exactly the weighted density divided by lambda, "
                            + "so its limiting coefficient is mc>0.")),
                    Paragraph(Text(
                        "This isolates the source's 'metric eats a power' mechanism without "
                            + "postulating the stated incomplete-Gamma expectation. The pinned "
                            + "Mathlib version has ordinary Gamma but no matching upper incomplete "
                            + "Gamma declaration; the special-function closed form therefore remains "
                            + "outside this theorem.")),
                    Paragraph(Text(
                        "Repository searches found no pseudo-Hermitian/GUE exponent theorem. "
                            + "Mathlib's Tendsto product law is used directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inverse-metric-linear-model-is-sharp"),
                DeclarationHandle.Create(Prefix + "inverse_metric_linear_model_is_sharp"),
                H("The one-power loss is sharp"),
                StatementSource.FromAuthor(SharpFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The explicit positive-side model w(lambda)=m/lambda and "
                        + "d(lambda)=c lambda squared realizes the hypotheses. Its weighted density "
                        + "is exactly mc lambda, while division by lambda squared diverges, so the "
                        + "linear exponent cannot be promoted back to a quadratic one."))),
                DescribeRole.Theorem))));

    private static Formula ReductionFormula() => Disp(Seq(
        F.Id("lambda w"), Open, F.Id("lambda"), Close, To, F.Id("m"), Comma, Quad,
        Frac, Grp(F.Id("d"), Open, F.Id("lambda"), Close),
        Grp(F.Id("lambda"), Caret, Grp(D(2))), To, F.Id("c"), Comma, Quad,
        F.Id("m"), Gt, D(0), Comma, Sp, F.Id("c"), Gt, D(0), Quad, Rightarrow, Quad,
        Frac,
        Grp(F.Id("w"), Open, F.Id("lambda"), Close,
            F.Id("d"), Open, F.Id("lambda"), Close),
        Grp(F.Id("lambda")), To, F.Id("mc")));

    private static Formula SharpFormula() => Disp(Seq(
        F.Id("w"), Open, F.Id("lambda"), Close, Eq,
        Frac, Grp(F.Id("m")), Grp(F.Id("lambda")), Comma, Quad,
        F.Id("d"), Open, F.Id("lambda"), Close, Eq,
        F.Id("c"), F.Id("lambda"), Caret, Grp(D(2)), Comma, Quad,
        F.Id("w"), Open, F.Id("lambda"), Close,
        F.Id("d"), Open, F.Id("lambda"), Close, Eq, F.Id("mc"), F.Id("lambda")));
}
