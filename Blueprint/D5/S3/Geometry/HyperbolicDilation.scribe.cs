using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class HyperbolicDilationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/HyperbolicDilation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive dilations of hyperbolic upper half-space.",
        H("Hyperbolic dilations"),
        Blocks(
            Paragraph(Text(
                "Scaling both horizontal coordinates and height by a positive real "
                    + "preserves the normalized upper half-space distance. The inverse "
                    + "scale gives an isometric equivalence. This does not establish "
                    + "completeness, curvature, cusp volume, or rigidity.")),
            Describe.Lean(
                DescribeId.Create("hyperbolic-positive-dilation"),
                DeclarationHandle.Create(Prefix + "positiveDilation"),
                H("Positive dilation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Scale every coordinate by the same positive real."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hyperbolic-dilation-distance"),
                DeclarationHandle.Create(Prefix + "hyperbolicDist_positiveDilation"),
                H("Distance preservation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Euclidean distance and height normalization scale equally."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hyperbolic-dilation-equivalence"),
                DeclarationHandle.Create(Prefix + "dilation"),
                H("Isometric equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive dilation has the inverse dilation by the reciprocal."))),
                DescribeRole.Definition)),
        []));
}
