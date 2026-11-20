using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LeaflessDartTourDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonbacktracking all-edge tours in finite graphs without leaves",
        H("Nonbacktracking all-edge tours in finite graphs without leaves"),
        Blocks(Describe.Lean(
            DescribeId.Create("leafless-dart-all-edge-tour"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LeaflessDartTour.exists_nonbacktracking_all_edge_tour"),
            H("Each prescribed dart begins and ends an all-edge walk"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("In a finite connected simple graph without vertices of degree one, every dart begins and ends a walk of length at least two whose consecutive underlying edges differ and whose edge set is the whole graph.")),
                Paragraph(Text("A connected graph of degree two admits a tour following its cycle. In the other case, deleting a prescribed edge leaves a cycle reachable from its head. This uses the two-leaf property of finite trees for a bridge and degree counting for a nonbridge. Traveling to the cycle, around it, and back yields a detour that replaces an immediate reversal. Concatenating reduced transitions through a list of darts then gives the covering walk.")),
                Paragraph(Text("Charatonik and Miklos used nonbacktracking edge walks to construct local expansions of finite graphs. The all-edge tour for every prescribed dart gives a choice of traversal for each edge in an exact graph map."))),
            DescribeRole.Theorem))));
}
