using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9SharedMidpointFiveAxesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separation confines the two shores' neighbors to disjoint subsets of the five active coordinates. Exterior cancellation forces both nonempty subsets to have even cardinalities, so both contain exactly two directions.",
        H("Two neighbors at a shared midpoint"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-neighbors-each"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedMidpointFiveAxes.two_neighbors_each"),
                H("Two neighbors at a shared midpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Separation confines the two shores' neighbors to disjoint subsets of the five active coordinates. Exterior cancellation forces both nonempty subsets to have even cardinalities, so both contain exactly two directions."))),
                DescribeRole.Theorem)),
        []));
}
