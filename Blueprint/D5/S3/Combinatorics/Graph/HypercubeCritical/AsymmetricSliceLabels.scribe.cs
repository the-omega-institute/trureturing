using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class AsymmetricSliceLabelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual asymmetric slice labels.", H("Actual asymmetric slice labels"),
        Blocks(Paragraph(Text(
            "Compress actual right vertices with two high neighbors into edges of the six-high core. Girth proves uniqueness and excludes triangles. The actual low right vertex anchors the distinguished pair, and degree saturation supplies six connectors and four stubs. The resulting eleven actual right labels are distinct and exhaust the right side. The declarations are private helpers consumed by AsymmetricSliceExclusion.result; they classify arbitrary finite graphs from the original hypotheses by symbolic graph and counting arguments."))),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceRigidity"))]));
}
