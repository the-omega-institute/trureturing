using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class BinaryTreeLeafDistanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dyadic distance sum in a complete binary tree.",
        H("Distances to the leaves of a complete binary tree"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-leaf-distance"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/Queries/BinaryTreeLeafDistance.weighted_leaf_distance"),
            H("The exact dyadic weight of all leaves"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Label every vertex by a Boolean word of length at most k, and connect it "
                    + "to the words obtained by appending one bit. The depth-k leaf list "
                    + "contains each depth-k word exactly once. For a vertex at depth d, "
                    + "weight each leaf by one half raised to the graph distance from that "
                    + "vertex. The total is three halves minus one half raised to the power (d + 1).")),
                Paragraph(Text(
                    "The distance is the number of edges from the starting word back to "
                    + "the longest common prefix and then forward to the target word. "
                    + "Transport the existing shortest pop and append paths to graph walks, "
                    + "preserving their lengths and the depth bound. "
                    + "At the root all leaves contribute a total of one. At a non-root vertex, "
                    + "the same first-bit branch retains the shorter-tree sum. All leaves in "
                    + "the other branch pass through the root and contribute one half raised "
                    + "to d plus one. Induction then evaluates the geometric sum."))),
            DescribeRole.Theorem))));
}
