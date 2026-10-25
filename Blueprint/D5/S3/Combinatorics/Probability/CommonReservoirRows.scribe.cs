using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class CommonReservoirRowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Probability/CommonReservoirRows.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct vertices and literal colours give independent actual star rows on a common tagged product space.",
        H("Star counts in the common reservoir"),
        Blocks(
            Paragraph(Text("Let V,C,A be finite and p in [0,1]. Sample every coordinate of the tagged sum V+C independently with parameter p. The maps vertex:A to V and colour:A to C are injective. A retained row selects both coordinates; a lost row selects at least one. All counts below are sums of the actual event indicators under this same law.")),
            Describe.Lean(DescribeId.Create("pair-lower"), DeclarationHandle.Create(Prefix + "pair_lower_tail"),
                H("Retained pairs"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every delta>=0, the probability that pairCount is at most (1-delta)p^2 card(A) is at most exp(-delta^2 p^2 card(A)/2). The rows are mutually independent because their two tagged supports are disjoint. Their exact expectations are p^2. Empty A and the endpoint values of p are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("loss-upper"), DeclarationHandle.Create(Prefix + "pair_loss_upper_tail"),
                H("Losses outside both reservoirs"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The probability that lossCount is at least 3p card(A) is at most exp(-p card(A)/5). A loss is the OR of vertex selection and literal-colour selection, with exact mean 2p-p^2. Apply the all-real mean-sensitive MGF estimate at log(3/2). The inequality log(3/2)>=2/5 gives the stated exponent. Retaining an edge outside both reservoirs is the complement of this OR."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("vertex-upper"), DeclarationHandle.Create(Prefix + "vertex_upper_tail"),
                H("Vertex reservoir size"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite V and C, the probability that vertexCount is at least 2p card(V) is at most exp(-p card(V)/3). The vertex evaluations form an independent subfamily of the same tagged coordinates. Their means equal p. Exponential Markov at log 2 and log 2>=2/3 prove the upper bound. These are classical Chernoff estimates."))), DescribeRole.Theorem))));
}
