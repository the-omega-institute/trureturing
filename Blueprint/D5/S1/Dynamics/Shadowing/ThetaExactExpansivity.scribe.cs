using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class ThetaExactExpansivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp finite positive expansivity on parallel-edge graphs",
        H("Sharp finite positive expansivity on parallel-edge graphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("parallel-edge-graph-exact-bowen-order"),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/ThetaExactExpansivity.exists_exact_order_on_graph"),
            H("A topologically exact map of order one below the valence"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every m at least two, the graph with two vertices and m plus one parallel edges admits a continuous surjection of least forward Bowen order m. Realize the m parallel arcs over one semicircle and identify the m copies of the other semicircle. The model is homeomorphic to the closed-edge quotient of the graph.")),
                Paragraph(Text("Identifying corresponding points of the negative semicircles across the labelled bouquet yields the graph map. Topological exactness descends from the bouquet, and projection to the circle semiconjugates the map to multiplication by m. Small forward Bowen balls are confined to one projection fiber. Distinct points over the same phase near a vertex have a common first image and witness the lower bound at every positive radius."))),
            DescribeRole.Theorem))));
}
