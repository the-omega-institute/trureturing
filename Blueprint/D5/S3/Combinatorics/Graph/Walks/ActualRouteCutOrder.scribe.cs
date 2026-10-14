using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualRouteCutOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualRouteCutOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual piece order and literal route support earn strict cut order and the concrete three fragments.",
        H("Ordered Cuts in an Actual Joined Route"),
        Blocks(
            Paragraph(Text("The vertex type and simple graph are arbitrary. All paths and cycle inventories refer to the literal supplied walks. These statements provide actual graph-surgery steps; an all-order recursive Hamilton construction is a separate consumer.")),
            Describe.Lean(DescribeId.Create("actual-ordered-path-is-join"),
                DeclarationHandle.Create(Prefix + "actual_ordered_path_is_join"),
                H("Identify the Supplied Actual Route"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Native adjacency supplies a Linked witness for the supplied ordered pieces. Equality of the supplied path support with their literal joined support then identifies the actual walks, keeping subsequent slicing on that same route."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-joined-route-cut-order"),
                DeclarationHandle.Create(Prefix + "actual_joined_route_cut_order"),
                H("Earn the Strict Cut Order"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directed cuts lie at valid local edge indices in two different route pieces. Literal full support locates them in the joined walk; the earlier piece contributes a smaller global index. The strict order and both directed endpoint pairs are conclusions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-joined-route-two-cut-slicing"),
                DeclarationHandle.Create(Prefix + "actual_joined_route_two_cut_slicing"),
                H("Slice the Same Actual Joined Route"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the two-cut construction at the just-earned strict indices of the supplied simple joined route. Three actual simple fragments retain its complete support and precisely its edges other than the two supplied cuts."))), DescribeRole.Theorem))));
}
