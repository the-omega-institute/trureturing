using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent;

internal sealed class Q9LaurentFiveTypeExclusionDocument : IScribeDocumentDefinition
{
    private const string Boundary =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Owner = Boundary + "Laurent/Q9LaurentFiveTypeExclusion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five opposite-parity direction triples are impossible.",
        H("Excluding five direction types in a cubic Laurent component"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-laurent-five-type-exclusion"),
                DeclarationHandle.Create(Owner + "card_directionTypes_ne_five"),
                H("Five opposite-parity direction triples are impossible"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Five types would give two partitions sharing a block. Projection away from that block gives four slices with threefold fibers and a common integer height. The box rigidity theorem excludes coexistence of both complementary splits. This removes a case of the one-sided Laurent approach to Hong, Wu and Xia’s Problem 2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-laurent-order-fifty-four"),
                DeclarationHandle.Create(Owner + "card_eq_fiftyFour_or_seven_le_directionTypes"),
                H("Fifty-four vertices or at least seven direction triples"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With at most three triples, the neighbor partition is constant. The projected boxes have one split and one center, so the projection has nine points. Its threefold fibers give twenty-seven vertices on the selected side. Cubic regularity gives the same number on the opposite side. The direction count gap and the five-type exclusion leave at least seven types at every other order."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Laurent/Q9LaurentDirectionTypes")),
         DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Laurent/Q9LaurentNormalizedBoxes")),
         DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9ProjectedHeightCompatibility"))]));
}
