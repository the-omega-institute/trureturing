using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class PointGapRadialGapPathDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/SpectralTopology/PointGapRadialGapPath.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A point-gap norm budget keeps the whole radial localizer path invertible.",
        H("Point-Gap Radial Gap Path"),
        Blocks(
            Definition("scale-gap-budget", "scaleGapBudget",
                "Scale gap budget",
                "The inverse zero-scale norm, scale norm, and position-direction "
                    + "norm form the explicit Neumann budget."),
            Definition("admissible-scale", "IsAdmissibleScale",
                "Admissible scale",
                "A scale is admissible when the spectral shift has a point gap "
                    + "and its explicit budget is below one."),
            Definition("radial-localizer", "radialLocalizer",
                "Radial localizer path",
                "The unit-interval parameter contracts the requested scale "
                    + "along the line from zero to the finite-scale localizer."),
            Theorem("zero-budget", "scale_gap_budget_zero",
                "Zero-scale budget",
                "The zero scale consumes no Neumann budget."),
            Theorem("radial-budget-monotone", "radial_scale_gap_budget_le",
                "Radial budget monotonicity",
                "Contracting a scale along the unit interval cannot increase "
                    + "its explicit gap budget."),
            Theorem("zero-admissible", "admissible_scale_zero",
                "Zero-scale admissibility",
                "Every point gap makes the zero scale admissible."),
            Theorem("star-shaped", "admissible_scale_radial",
                "Star-shaped admissible region",
                "Every radial contraction of an admissible scale remains admissible."),
            Theorem("radial-affine", "radial_localizer_affine",
                "Affine radial localizer",
                "The radial family is the zero-scale localizer plus the linearly "
                    + "scaled position direction."),
            Theorem("radial-start", "radial_localizer_zero",
                "Radial path start",
                "The radial path starts at the zero-scale localizer."),
            Theorem("radial-end", "radial_localizer_one",
                "Radial path endpoint",
                "The radial path ends at the requested finite-scale localizer."),
            Theorem("radial-hermitian", "radial_localizer_isHermitian",
                "Radial Hermitianity",
                "A Hermitian position observable makes every radial-path matrix Hermitian."),
            Theorem("radial-unit", "radial_localizer_isUnit",
                "Radial gap preservation",
                "Every point on an admissible radial segment is invertible."),
            Theorem("hermitian-gap-path", "radial_hermitian_gap_path",
                "Hermitian invertible radial path",
                "An admissible scale supplies a Hermitian invertible path on "
                    + "the whole unit interval."),
            Theorem("closure-budget", "one_le_scale_gap_budget_of_gap_closure",
                "Gap-closure budget obstruction",
                "Any finite-scale gap closure above a point-gap zero scale "
                    + "forces the explicit budget to reach at least one."),
            Theorem("radial-closure-budget", "one_le_endpoint_budget_of_radial_gap_closure",
                "Radial gap-closure obstruction",
                "A gap closure anywhere on the radial segment forces the "
                    + "endpoint budget to reach at least one."),
            Theorem("exact-inertia-path", "point_gap_exact_inertia_and_radial_gap_path",
                "Exact initial inertia with radial gap path",
                "A point gap supplies exact initial chiral inertia and a "
                    + "Hermitian invertible path to every admissible scale.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/SpectralTopology/PointGapFiniteScaleStability")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/SpectralTopology/PointGapExactInertia")),
        ]));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);
}