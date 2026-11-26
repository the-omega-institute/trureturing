using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class WordTreeCutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The components obtained by deleting a parent edge in a finite binary tree.",
        H("Cutting off a child subtree"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("below-child"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/WordTreeCut.belowChild"),
                H("Membership in the selected child subtree"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A vertex belongs to the child subtree when its word has the child word " +
                    "as a prefix. The child word is the parent word followed by the chosen bit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bounded-reachable-after-extension-cut"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/WordTreeCut.bounded_reachable_after_extension_cut"),
                H("Reachability is equality of subtree membership after the cut"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a depth cap, a parent vertex and a chosen bit with its child " +
                        "still inside the depth cap. Delete the edge joining parent and child. " +
                        "Two vertices are reachable from one another exactly when they agree " +
                        "on membership in the selected child subtree.")),
                    Paragraph(Text(
                        "An edge crossing the prefix boundary must join the selected child " +
                        "to its parent. Hence every remaining walk preserves membership. " +
                        "Inside the subtree, each vertex connects to the child by a chain of " +
                        "extensions. Outside the subtree, each vertex connects to the empty " +
                        "word by a chain of extensions. These chains respect the depth cap " +
                        "and avoid the deleted edge."))),
                DescribeRole.Theorem))));
}
