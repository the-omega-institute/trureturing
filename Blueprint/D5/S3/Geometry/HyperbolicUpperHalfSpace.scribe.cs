using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class HyperbolicUpperHalfSpaceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/HyperbolicUpperHalfSpace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Ptolemy proof of the upper half-space metric and horizontal isometries.",
        H("Hyperbolic upper half-space metric"),
        Blocks(
            Paragraph(Text(
                "Positive-height coordinates carry the standard upper half-space distance. "
                    + "A reflected-point Ptolemy estimate proves its metric laws in any real "
                    + "inner product horizontal space. Horizontal translations give a faithful "
                    + "isometric action. Curvature, completeness, finite volume, cusps, and "
                    + "Mostow--Prasad rigidity are not established by these declarations.")),
            Describe.Lean(
                DescribeId.Create("hyperbolic-upper-half-coordinates"),
                DeclarationHandle.Create(Prefix + "UpperHalfSpace"),
                H("Positive-height coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Points of a Euclidean product with positive height."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hyperbolic-upper-half-distance"),
                DeclarationHandle.Create(Prefix + "hyperbolicDist"),
                H("Upper half-space distance formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Twice the inverse hyperbolic sine of the normalized Euclidean separation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hyperbolic-upper-half-triangle"),
                DeclarationHandle.Create(Prefix + "hyperbolicDist_triangle"),
                H("Triangle inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reflection and Euclidean Ptolemy yield the hyperbolic triangle inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hyperbolic-upper-half-metric"),
                DeclarationHandle.Create(Prefix + "hyperbolicMetricSpace"),
                H("Metric-space instance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The distance formula equips the distinct upper half-space type with a metric."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hyperbolic-upper-half-representation"),
                DeclarationHandle.Create(Prefix + "horizontalRepresentation"),
                H("Horizontal isometric representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Horizontal addition acts through hyperbolic isometries."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hyperbolic-upper-half-fixed"),
                DeclarationHandle.Create(Prefix + "horizontalTranslation_fixed_iff_zero"),
                H("Fixed point criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A horizontal translation fixing one point has zero translation vector."))),
                DescribeRole.Theorem)),
        []));
}
