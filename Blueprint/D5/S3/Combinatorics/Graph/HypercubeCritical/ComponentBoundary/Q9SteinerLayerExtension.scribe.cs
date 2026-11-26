using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SteinerLayerExtensionDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp extension bound for Steiner supports in Q9",
        H("Steiner reconstruction and the sharp extension bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-steiner-layer-reconstruction"),
                DeclarationHandle.Create(Owner + "missing_triples_steiner"),
                H("The missing triples form a Steiner triple system"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A cubic support of size 144 in layers 3 and 4 has 72 vertices in each layer. Each selected triple has three of its six upper neighbors outside the support. This yields 216 incidences with the 54 omitted four-sets, so every omitted four-set contains four selected triples.")),
                    Paragraph(Text("Every selected four-set contains exactly one missing triple by cubicity. Two missing triples can never share a pair because their union would then be a four-set containing both. The twelve missing triples cover all 36 pairs exactly once."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-steiner-residual-layers"),
                DeclarationHandle.Create(Owner + "mem_residual_iff"),
                H("The closed-neighborhood complement consists of six layers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every pair belongs to six selected triples. Every five-set contains a missing triple because its ten pairs could otherwise be completed only at the four outside points, with each outside point completing a matching of size at most two. Thus the closed neighborhood contains every vertex of layers 2 through 5."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-steiner-extension-cap"),
                DeclarationHandle.Create(Owner + "extension_card_le"),
                H("A subcubic extension has at most 246 vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every added vertex lies outside the closed neighborhood, since the original support is already cubic. Let k be the number of retained layer-7 vertices and d the number of omitted layer-6 vertices. Each retained vertex has at least four omitted lower neighbors, while each omitted lower vertex can serve at most three retained upper vertices. Hence 4k ≤ 3d, and d + 36 − k is at least 36.")),
                    Paragraph(Text("The separate nine-leaf stars on layers 0 and 1 and on layers 8 and 9 each require another omission. The six residual layers have 140 vertices, so the complete extension has at most 144 + 140 − 38 = 246 vertices. This excludes the Steiner family from the 258-vertex case of the external problem. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-steiner-unique-extension"),
                DeclarationHandle.Create(Owner + "extension_card_eq_iff"),
                H("Exactly one extension attains 246 vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Keeping any layer-7 vertex makes the middle omission bound strict. A star with exactly one omission must lose its center. Thus equality forces the omission of layers 0, 7 and 9 and the retention of layers 1, 6 and 8. These three retained layers have no edges between them, so they attain the bound."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation"))
        ]));
}
