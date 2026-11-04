using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Jacobi;

internal sealed class LeafPruningRanksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Jacobi/LeafPruningRanks.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chronological leaf deletion and component boundaries", H("Chronological leaf deletion and component boundaries"),
        Blocks(
            Describe.Lean(DescribeId.Create("pruning-ranks-leafranks"),
                DeclarationHandle.Create(Prefix + "LeafRanks"), H("Chronological leaf-deletion ranks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A vertex scheduled before the cut has at most one adjacent vertex whose rank is no smaller. This generic graph condition is the live input extracted from the literal flag-counted deletion chronology."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pruning-ranks-deleted-acyclic"),
                DeclarationHandle.Create(Prefix + "deleted_acyclic"), H("Deleted vertices induce a forest"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A cycle would have a minimum-rank vertex with two distinct later neighbors. Therefore the graph induced by ranks below the cut is acyclic."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pruning-ranks-cycle-retained"),
                DeclarationHandle.Create(Prefix + "cycle_retained"), H("Every actual cycle survives the cut"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The minimum rank on a cycle cannot lie below the cut; every vertex of that cycle is retained. No cycle-existence hypothesis is inserted into the rank structure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pruning-ranks-retained-path"),
                DeclarationHandle.Create(Prefix + "retained_path"), H("Simple paths between retained vertices stay retained"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If such a path dipped below the cut, its minimum-rank internal vertex would have distinct predecessor and successor of no smaller rank, contradicting the actual one-later-neighbor condition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pruning-ranks-retained-connected"),
                DeclarationHandle.Create(Prefix + "retained_connected"), H("The nonempty retained core is connected"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a connected source and a nonempty retained vertex set, a source simple path between retained endpoints remains in the retained induced graph. This is consumed in the actual flag pruning extraction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pruning-ranks-componentboundary"),
                DeclarationHandle.Create(Prefix + "ComponentBoundary"), H("An actual boundary adjacency"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A boundary records a deleted-component vertex, its component membership, a retained exterior vertex and their literal adjacency. It is not a postulated unique-root structure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pruning-ranks-component-boundary-unique"),
                DeclarationHandle.Create(Prefix + "component_boundary_unique"), H("A deleted component has at most one boundary adjacency"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A simple deleted path between two proposed boundary adjacencies forces its earliest vertex to have two later neighbors. Thus both interior and exterior endpoints agree."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pruning-ranks-component-boundary-nonempty"),
                DeclarationHandle.Create(Prefix + "component_boundary_nonempty"), H("A deleted component of a connected source reaches the retained core"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the connected source has any retained vertex, a path from a deleted component to that vertex has a first cut-crossing edge. Its deleted endpoint remains in the original component, furnishing an actual boundary. Together with uniqueness this supplies the real root used by flag pruning."))), DescribeRole.Theorem))));
}
