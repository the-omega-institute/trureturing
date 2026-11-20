using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class SphereRatioEarlierExamplesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/SphereRatioEarlierExamples.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mazhang2026scaleddowndate");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sphere-ratio infima: h = 1 gives 1/√d in dimension d, 0 overall and 1/√2 in dimensions at most two; h(t) = 1/t gives 0.",
        H("Infima for the earlier examples of the sphere question"),
        Blocks(
            Describe.Lean(DescribeId.Create("sphere-ratio-def"),
                DeclarationHandle.Create(Prefix + "ratio"), H("The sphere ratio"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For h : ℝ → ℝ and x ∈ ℝᵈ, R_h(x) = Σᵢ xᵢ h(xᵢ) / (Σᵢ h(xᵢ)²)^{1/2}."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sphere-ratio-values-def"),
                DeclarationHandle.Create(Prefix + "values"), H("Values on active unit vectors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The set of values R_h(x) over unit vectors x ∈ ℝᵈ with every coordinate positive: the "
                    + "active-coordinate convention, in which zero coordinates are omitted and d counts the "
                    + "active coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sphere-ratio-earlier-examples"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Infima for h = 1 and h(t) = 1/t"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For h = 1: in every fixed dimension d ≥ 1 the infimum of R_h is 1/√d, and it is not "
                        + "attained when d ≥ 2; over all dimensions the infimum is 0 and every value is "
                        + "positive; over dimensions at most two the infimum is 1/√2 and every value exceeds it. "
                        + "For h(t) = 1/t: in every dimension d ≥ 2, in particular already in dimension two, the "
                        + "infimum is 0 and every value is positive.")),
                    Paragraph(Text(
                        "For h = 1, R_h(x) = (Σᵢ xᵢ)/√d. Each 0 < xᵢ ≤ 1 gives xᵢ² ≤ xᵢ, so Σᵢ xᵢ ≥ 1, strictly "
                        + "when d ≥ 2 because then some xᵢ < 1. Vectors with one coordinate (1 − (d − 1)ε²)^{1/2} "
                        + "and d − 1 coordinates ε give R_h → 1/√d as ε → 0; choosing d large then gives the "
                        + "all-dimension infimum 0, and dimension one gives the value 1 > 1/√2. For h(t) = 1/t, "
                        + "R_h(x) = d/(Σᵢ xᵢ⁻²)^{1/2} ≤ d√p when one squared coordinate is p, and p → 0 drives "
                        + "the ratio to 0. This is Corollary 10 of H. Ma and W. Zhang "
                        + "(DOI 10.5281/zenodo.23920598). The example h = 1 was suggested by daw (comment "
                        + "11110291) and h(t) = 1/t was used by Exodd (answer 5146715) on Lucid's sphere "
                        + "question, Mathematics Stack Exchange 5146381, linked from MathOverflow 513954, "
                        + "revision 2."))),
                DescribeRole.Theorem))));
}
