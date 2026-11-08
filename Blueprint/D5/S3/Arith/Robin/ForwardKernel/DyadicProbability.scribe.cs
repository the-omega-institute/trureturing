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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-position-map"),
                DeclarationHandle.Create(Prefix + "dyadic_position_map"),
                H("Law of the scaled position"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For X>0, the image of mu_X under x maps to x/X is mu_1. "
                    + "The substitution x=Xu cancels X in the logarithmic density, "
                    + "so the position law on [1,2] does not depend on X."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("block-mass"),
                DeclarationHandle.Create(Prefix + "block_mass"),
                H("Exact logarithmic block mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If 1<=u<=v<=2, the probability of [u,v] under mu_1 is "
                    + "log(v/u)/log(2). Restricting the density to the subinterval "
                    + "reduces the mass to the integral of 1/(x log(2)); its "
                    + "endpoints have zero Lebesgue measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("position-indicator-icc-ae-eq-ioc"),
                DeclarationHandle.Create(Prefix + "position_indicator_Icc_ae_eq_Ioc"),
                H("Endpoint conventions for position blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For X>0 and any real endpoints u,v, composing the [u,v] "
                    + "and (u,v] indicators of an arbitrary real function with "
                    + "x/X gives equal functions almost everywhere under mu_X. "
                    + "The position law is mu_1, which assigns zero mass to "
                    + "singletons. Thus a fixed-scale hypothesis stated with "
                    + "closed blocks also applies to disjoint left-open blocks."))),
                DescribeRole.Theorem))));
}
