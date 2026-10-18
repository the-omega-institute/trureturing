using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalCactusGateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each component left after deleting the edges of a cactus cycle has exactly one attachment vertex on the cycle.",
        H("A cycle gives unique gates in a cactus"),
        Blocks(
            Describe.Lean(DescribeId.Create("three-terminal-cactus-cycle-gate"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCactusGate.cycle_gate"),
                H("Existence and uniqueness of the gate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let G be any connected simple graph on a decidable vertex type, and assume that "
                    + "two simple cycles with distinct undirected edge sets have at most one common vertex. "
                    + "Fix a simple cycle C. For every vertex x, there is exactly one vertex g of C "
                    + "reachable from x after every edge of C has been deleted. No finiteness hypothesis "
                    + "is needed. Existence follows a walk from x until its first visit to C. For uniqueness, "
                    + "an outside path between two distinct vertices of C and a path inside C contain "
                    + "two subpaths whose concatenation is a simple cycle. This new cycle contains an "
                    + "edge outside C and shares the two distinct subpath endpoints with C, contradicting "
                    + "the cactus condition. Thus every connected component of the deleted graph meets "
                    + "C in precisely one vertex."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("three-terminal-cactus-side-graph"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCactusGate.sideGraph"),
                H("The two actual edge families"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a simple graph G and a vertex set A, sideGraph G A has the same vertex type as G. "
                    + "An edge is present exactly when it is an edge of G and both endpoints belong to A. "
                    + "Vertices outside A are isolated."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("three-terminal-cactus-component-decomposition"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCactusGate.cycle_component_decomposition"),
                H("An exact one-vertex decomposition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same connected cactus and simple-cycle hypotheses, fix x and let A be "
                    + "its component after deleting the cycle edges. There is a gate g in both A and C. "
                    + "Set B to the complement of A together with g. The original graph is exactly the "
                    + "union of sideGraph G A and sideGraph G B. Each graph has all its edges on its own "
                    + "side, the sides meet only at g, and their edge sets are disjoint. Moreover the "
                    + "left edge set contains no edge of C, and the original graph induced on either "
                    + "side is connected. Indeed, an edge leaving A must be a cycle "
                    + "edge, and its endpoint in A is then the unique gate. A cycle edge with both "
                    + "endpoints in A would have both endpoints equal to g, contrary to simplicity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("three-terminal-cactus-spanning-cycle"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCactusGate.cycle_spanning_edges"),
                H("A spanning cycle contains every edge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let C be a simple cycle in a cactus. If every vertex belongs to the support of C, "
                    + "then the graph edge set equals the edge set of C. An additional edge would join "
                    + "two cycle vertices in the graph with all cycle edges deleted. The unique-gate "
                    + "property forces those endpoints to coincide, contrary to the absence of loops. "
                    + "Neither connectedness nor finiteness is required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("three-terminal-cactus-strict-component-edges"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCactusGate.cycle_component_strict_edges"),
                H("Strict decrease on both induced sides"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume additionally that the vertex type is finite and x lies outside C. The same "
                    + "component A, unique gate g, and side B give an edge-disjoint one-vertex union. "
                    + "Both induced graphs remain connected cacti, both side edge sets are nonempty proper "
                    + "subsets of the original edge set, and each induced graph has strictly fewer "
                    + "edges than the original graph. A path from x to g supplies a left edge. Every "
                    + "edge of C lies on the right, supplying a right edge. Disjointness makes both "
                    + "inclusions strict; the subtype embeddings transfer these strict finite "
                    + "cardinality bounds to the induced graphs."))), DescribeRole.Theorem)),
        []));
}
