using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class FirstObservedCycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The edge that closes the first cycle in an exploration with complete neighborhoods.",
        H("When a rooted exploration first observes a cycle"),
        Blocks(Describe.Lean(
            DescribeId.Create("first-observed-cycle"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/Queries/FirstObservedCycle.first_observed_cycle"),
            H("Criterion for a first observed cycle"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Start from a root in a finite simple graph. At every step query the complete "
                + "neighborhood of a vertex reachable from the root through exposed edges. "
                + "The exposed graph contains exactly the original edges incident to vertices "
                + "already queried. Assume this graph is acyclic before the next query. The "
                + "reply creates a cycle exactly when the next vertex has never been queried "
                + "and it has a neighbor that is also unqueried and reachable from the root "
                + "before the query. Adding that edge joins two vertices already connected "
                + "by exposed edges. When every new edge reaches an isolated vertex, these "
                + "edges add only leaves."))),
            DescribeRole.Theorem))));
}
