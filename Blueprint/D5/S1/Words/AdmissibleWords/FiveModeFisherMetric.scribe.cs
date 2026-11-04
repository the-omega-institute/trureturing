using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class FiveModeFisherMetricDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AdmissibleWords/FiveModeFisherMetric.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual four-dimensional affine chart of positive five-mode laws "
            + "carries a smooth Fisher metric on its tangent bundle.",
        H("The five-mode Fisher Riemannian metric"),
        Blocks(
            Paragraph(Text(
                "Coordinates are functions from Fin 4 to the reals. simplexDomain "
                    + "is the open subset chartDomain from FiveModeFisherImmersion, "
                    + "and FiveModeManifold is its subtype. The smooth structure is "
                    + "the one inherited from that open subset of the real normed space.")),
            Describe.Lean(
                DescribeId.Create("fisher-metric-form"),
                DeclarationHandle.Create(Prefix + "fisherMetricForm"),
                H("The continuous bilinear form in chart coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each q the form is the sum over s in Fin 5 of the inverse "
                        + "probability simplexLaw(q)(s) times the product of the two "
                        + "s-coordinate projections of tangentLift. Its value on "
                        + "u and v is exactly "
                        + "fisher(simplexLaw(q),tangentLift(u),tangentLift(v))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fisher-riemannian-metric"),
                DeclarationHandle.Create(Prefix + "fisherRiemannianMetric"),
                H("A smooth metric on the actual tangent bundle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "fisherRiemannianMetric is a "
                            + "Bundle.ContMDiffRiemannianMetric with smoothness "
                            + "order infinity and model space Fin 4 to the reals, "
                            + "on TangentSpace at each point of FiveModeManifold. "
                            + "Its inner form is fisherMetricForm. Symmetry follows "
                            + "from commutation of the two tangent factors; strict "
                            + "positivity is supplied by the square-root immersion.")),
                    Paragraph(Text(
                        "For a positive normalized law, each probability is at "
                            + "most one. A metric unit ball therefore bounds each "
                            + "coordinate of a tangent vector by one, giving the "
                            + "required boundedness property. Smoothness follows "
                            + "from smooth affine probabilities and inversion on "
                            + "their positive domain, with the open-subset tangent "
                            + "trivializations identified explicitly.")),
                    Paragraph(Text(
                        "The associated fisherRiemannianBundle instance supplies "
                            + "the Riemannian bundle structure. Lean synthesizes "
                            + "both IsContMDiffRiemannianBundle at order infinity "
                            + "and IsContinuousRiemannianBundle. This construction "
                            + "establishes a probability-manifold metric; it does "
                            + "not assert geodesic completeness, curvature bounds "
                            + "or a relation between its spectrum and the Riemann hypothesis."))),
                DescribeRole.Definition))));
}
