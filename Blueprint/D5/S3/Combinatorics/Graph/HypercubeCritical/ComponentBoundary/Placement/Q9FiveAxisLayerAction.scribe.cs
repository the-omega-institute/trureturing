using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisLayerActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exchanging coordinates 3 and 4 and exchanging the roots realize the two pattern permutations by actual cube isometries. Both preserve the even slice and the mask family.",
        H("The action on actual supports"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reaches-representative"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisLayerAction.reaches_representative"),
                H("The action on actual supports"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Swapping coordinates 3 and 4 fixes the root pair and the missing mask. Translation by the root displacement exchanges the roots, and exchanging the two components restores their order. The two operations commute and are involutions on the rooted layer, so each orbit has at most four patterns. The certificate cover finds six orbits among the eighteen patterns. The same operations transport actual cube supports while preserving the even slice and the mask family."))),
                DescribeRole.Theorem)),
        []));
}
