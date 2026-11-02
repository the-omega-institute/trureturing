using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class WeavingStateGraphBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual mixed-circle state polynomial.",H("The actual mixed-circle state polynomial"),Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Topology/WeavingStateGraphBridge.graphStatePolynomial_eq_mixed"),
                H("The actual mixed-circle state polynomial"),StatementSource.FromLean(),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Map a crossing subset to graph edges using the actual crossing-edge bijection and the uniform-circle vertex order. On the full vertex set, the graph of that state is isomorphic to the original spanning reference graph, including its isolated vertices. Its canonical graphRank is the actual rank q(S), and its state exponent is c(S)-1 by the arbitrary-state circle identity and positivity. The crossing-edge equivalence induces an equivalence on finite subsets. Reindexing the finite sum identifies the canonical graphStatePolynomial with the literal mixed-circle state polynomial term by term. No Jones invariant is defined by this polynomial."))),DescribeRole.Theorem))));
}
