using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class CommonReservoirGraphDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Probability/CommonReservoirGraph.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual rainbow two-edge choices and deterministic predecessor sets are counted on one common reservoir outcome.",
        H("Graph counts in the common reservoir"),
        Blocks(
            Describe.Lean(DescribeId.Create("graph-base"), DeclarationHandle.Create(Prefix + "graph_base_lower_tail"),
                H("Rainbow base choices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let G be a loopless directed graph on a nonempty finite V, with colours in finite C. Require injectivity separately on every outgoing and every incoming star. Let p be in [0,1], nu>0 and n=card(V). For arbitrary u,w, remove the actual exceptional endpoints with more than nu n/16 repeated-colour two-edge choices. Suppose w is outside that set and there are at least nu n/4 actual two-edge middle vertices. If Tb<3p^3 nu n/64, then the probability that fewer than Tb rainbow choices have their middle vertex and both distinct literal colours selected is at most exp(-9p^3 nu n/512).")),
                    Paragraph(Text("The deterministic rainbow choice core gives at least 3nu n/16 choices and three classes of disjoint tagged supports. Coincident u=w is included by the same repeated-colour partition count. The triple-selection estimate applies at delta=3/4 with exact mean p^3 times the number of rainbow choices. No assertion that every two-edge choice is rainbow, or that different classes are independent, is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("graph-incoming"), DeclarationHandle.Create(Prefix + "graph_incoming_lower_tail"),
                H("A fixed predecessor set"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let V,C be finite, p in [0,1], and require proper incoming colours. Fix a deterministic vertex set L and vertex w before sampling. For every delta>=0, the probability that the selected vertex-and-colour incoming count is at most (1-delta)p^2 card(incoming(G,L,w)) is at most exp(-delta^2 p^2 card(incoming(G,L,w))/2). The incoming vertices and colours are distinct, so the actual rows are mutually independent on the common tagged law."))), DescribeRole.Theorem))));
}
