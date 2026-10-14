using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class BipartiteThresholdRoundingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite opposite-colour threshold intersection has the exact positive-part count used by continuation VI.",
        H("Bipartite Threshold Rounding"),
        Blocks(Describe.Lean(
            DescribeId.Create("kbonacci-bipartite-threshold-count"),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/BipartiteThresholdRounding.cross_threshold_card"),
            H("Opposite-colour threshold count"),
            StatementSource.FromAuthor(Disp(Seq(
                Call("card", Call("crossThresholds", F.Id("N"), F.Id("a"), F.Id("b"))),
                Sp, Eq, Sp, F.Id("a"), Sp, Plus, Sp, F.Id("b"), Sp, Minus, Sp, F.Id("N")))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For natural N, a and b with a <= N and b <= N, "
                    + "crossThresholds N a b contains exactly those finite uniform thresholds "
                    + "t with N-b <= t < a. Its cardinality is the truncated difference "
                    + "a+b-N, including the empty intersection and endpoint cases.")),
                Paragraph(Text(
                    "This is the discrete counting identity behind the expectation "
                    + "max(0,x+y-1) in the bipartite relaxation used by Theorem 183.2. "
                    + "It does not assert an acquisition strategy, a probability law, "
                    + "or the full conditioned all-word criterion."))),
            DescribeRole.Theorem))));
}
