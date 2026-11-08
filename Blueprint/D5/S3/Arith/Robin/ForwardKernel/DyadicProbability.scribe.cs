using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class DyadicProbabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized logarithmic integration on a positive dyadic interval is a probability measure.",
        H("Dyadic logarithmic probability"),
        Blocks(
            Paragraph(Text(
                "For X>0, let mu_X be Lebesgue measure restricted to (X,2X], "
                + "with density 1/(x*log(2)). The endpoints have zero Lebesgue measure, "
                + "so this also represents logarithmic integration over [X,2X].")),
            Describe.Lean(
                DescribeId.Create("dyadic-probability-measure"),
                DeclarationHandle.Create(Prefix + "dyadicProbabilityMeasure"),
                H("Normalized logarithmic measure on a dyadic interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real X, the dyadic measure is Lebesgue measure restricted to (X,2X], with density given by the nonnegative part of 1/(x*log(2)). For X>0 this is the logarithmic probability measure dx/(x*log(2))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dyadic-probability-measure-integral"),
                DeclarationHandle.Create(Prefix + "dyadicProbabilityMeasure_integral"),
                H("Conversion to logarithmic integration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For X>0 and every real-valued function f, the integral of f against "
                    + "mu_X equals the interval integral of f(x)/x from X to 2X, divided "
                    + "by log(2). The identity uses the total Bochner integral, so it "
                    + "also applies without an integrability premise. Substituting f(x)^2 "
                    + "or abs(f(x))^4 gives the corresponding moment conversions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-probability-measure-integrable"),
                DeclarationHandle.Create(Prefix + "dyadicProbabilityMeasure_integrable"),
                H("Conversion of integrability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For X>0, interval integrability of f(x)/x on [X,2X] implies "
                    + "integrability of f with respect to mu_X. Multiplication by the "
                    + "constant 1/log(2) and the density criterion for integrability "
                    + "give the result."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-probability-measure-univ"),
                DeclarationHandle.Create(Prefix + "dyadicProbabilityMeasure_univ"),
                H("Unit total mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For X>0, mu_X assigns mass one to the whole real line. The density "
                    + "is continuous and nonnegative on [X,2X], and its integral is "
                    + "log((2X)/X)/log(2)=1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-probability-measure-is-probability-measure"),
                DeclarationHandle.Create(Prefix + "dyadicProbabilityMeasure_isProbabilityMeasure"),
                H("Probability measure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive X, the normalized logarithmic measure mu_X "
                    + "is a probability measure, since its total mass is one."))),
                DescribeRole.Theorem))));
}
