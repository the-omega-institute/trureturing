using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class HyperbolicCompletenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/HyperbolicCompleteness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completeness of the hyperbolic upper-half-space metric.",
        H("Hyperbolic completeness"),
        Blocks(
            Paragraph(Text(
                "When the horizontal real inner product space is complete, its hyperbolic "
                    + "upper half-space is complete. A hyperbolic Cauchy sequence has Cauchy "
                    + "Euclidean coordinates and Cauchy logarithmic heights; the limiting "
                    + "height remains positive. This establishes completeness of the model. "
                    + "Manifold curvature, quotient completeness, finite-volume cusps, and "
                    + "Mostow--Prasad rigidity remain separate obligations.")),
            Describe.Lean(
                DescribeId.Create("hyperbolic-log-height-bound"),
                DeclarationHandle.Create(Prefix + "dist_log_height_le"),
                H("Logarithmic height bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The difference of log-heights is bounded by the normalized distance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hyperbolic-complete-space"),
                DeclarationHandle.Create(Prefix + "hyperbolicCompleteSpace"),
                H("Complete-space instance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coordinate completeness and the positive exponential limit of height yield hyperbolic convergence."))),
                DescribeRole.Definition)),
        []));
}
