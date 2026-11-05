using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class FiveModeFisherImmersionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AdmissibleWords/FiveModeFisherImmersion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The open five-mode probability simplex has a global affine chart whose "
            + "square-root immersion pulls Euclidean pairing back to the Fisher form.",
        H("A smooth Fisher immersion of the five-mode simplex"),
        Blocks(
            Paragraph(Text(
                "Use four real coordinates q. The tangent lift has coordinate zero "
                    + "equal to minus the sum of q and coordinate i.succ equal to q(i). "
                    + "simplexLaw(q) adds one in coordinate zero, so its five coordinates "
                    + "sum to one. The chart domain requires each of these coordinates "
                    + "to be strictly positive.")),
            Paragraph(Text(
                "The square-root chart has coordinates 2*sqrt(simplexLaw(q)(s)). "
                    + "Its derivative sends u to tangentLift(u)(s) divided by "
                    + "sqrt(simplexLaw(q)(s)). Positivity of the probabilities keeps "
                    + "all denominators nonzero. This is the classical categorical "
                    + "Fisher construction, implemented here on the actual four "
                    + "affine coordinates rather than an unspecified ambient metric.")),
            Describe.Lean(
                DescribeId.Create("five-mode-fisher-chart-immersion"),
                DeclarationHandle.Create(Prefix + "five_mode_fisher_chart_immersion"),
                H("Global chart, immersion, and exact pullback"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The chart domain is open. For every q, membership in that "
                            + "domain is equivalent to simplexLaw(q) belonging to "
                            + "openSimplex. For each positive normalized law p there "
                            + "exists exactly one q in the chart domain with "
                            + "simplexLaw(q) = p.")),
                    Paragraph(Text(
                        "The square-root chart is infinitely continuously "
                            + "differentiable on the chart domain. At every q in the "
                            + "domain it has the stated Frechet derivative, and this "
                            + "continuous linear derivative is injective. The sum of "
                            + "squares of the five chart coordinates is four, so the "
                            + "image lies on the sphere of radius two.")),
                    Paragraph(Text(
                        "For all four-dimensional directions u and v, the sum over "
                            + "s of squareRootDerivative(q)(u)(s) times "
                            + "squareRootDerivative(q)(v)(s) equals "
                            + "fisher(simplexLaw(q),tangentLift(u),tangentLift(v)). "
                            + "For every nonzero u that Fisher quadratic form is "
                            + "strictly positive. These statements describe the "
                            + "simplex geometry; no arithmetic spectral operator or "
                            + "transport to zeta zeros is supplied."))),
                DescribeRole.Theorem))));
}
