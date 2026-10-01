using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class HyperbolicTopologyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/HyperbolicTopology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Topology and compact closed balls of hyperbolic upper half-space.",
        H("Hyperbolic topology"),
        Blocks(
            Paragraph(Text(
                "The normalized hyperbolic metric induces the usual topology on the "
                    + "positive-height upper half-space over any real inner product space. "
                    + "When the horizontal metric space is proper, all hyperbolic closed "
                    + "balls are compact. The proof controls height above and below and "
                    + "bounds horizontal separation on each ball. This concerns the model "
                    + "space; manifold curvature, quotient completeness, finite-volume "
                    + "cusps, and Mostow--Prasad rigidity remain separate obligations.")),
            Describe.Lean(
                DescribeId.Create("hyperbolic-coordinate-homeomorphism"),
                DeclarationHandle.Create(Prefix + "coordinatesHomeomorph"),
                H("Coordinate homeomorphism"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate bijection is continuous in both directions, using "
                        + "the logarithmic height estimate and the exact distance formula."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hyperbolic-proper-space"),
                DeclarationHandle.Create(Prefix + "hyperbolicProperSpace"),
                H("Proper-space instance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A hyperbolic closed ball is a closed subset of the continuous "
                        + "image of a compact horizontal ball times a positive height interval."))),
                DescribeRole.Definition)),
        []));
}
