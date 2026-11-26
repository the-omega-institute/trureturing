using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class DistanceThreeTripleFamilyBoundDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "DistanceThreeTripleFamilyBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower bound for triple families with restricted pair degrees.",
        H("At least eighteen triples"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("distance-three-pair-codegree"),
                DeclarationHandle.Create(Owner + "codegree"),
                H("Codegree of a face"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Count the selected triples containing the face."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("distance-three-triple-family-eighteen"),
                DeclarationHandle.Create(Owner + "card_ge_eighteen"),
                H("The eighteen-triple lower bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take a nonempty family of triples. Every occurring pair has codegree two "
                    + "or three, each triple contains at most one pair of codegree two, "
                    + "and each four-set contains at most two selected triples. The three "
                    + "pairs of a selected triple allow at least five "
                    + "extensions to other triples. Their new axes are distinct because every "
                    + "four-set contains at most two selected triples. In an axis link, the "
                    + "three neighbors of a degree-three axis are independent and each has "
                    + "degree at least two. Thus every link has at least six edges. At eight "
                    + "axes the pair-degree counts force the family size to be divisible by "
                    + "six. These estimates give eighteen triples in all cases."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "MinimumContactDisplacementCount")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "TripleContactFamilyBound"))
        ]));
}
