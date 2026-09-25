using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class EdgeConnectivityDecodingDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Fourier/CharacterSelection/EdgeConnectivityDecoding."
            + "edge_gradient_unique_recovery";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Edge connectivity gives deterministic unique recovery of a binary edge gradient "
            + "under fewer than half the cut size in arbitrary edge errors.",
        H("Edge Connectivity and Binary Gradient Decoding"),
        Blocks(Describe.Lean(
            DescribeId.Create("edge-gradient-unique-recovery"),
            DeclarationHandle.Create(Declaration),
            H("Unique recovery of a noisy binary edge gradient"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be a simple graph with finitely many edges, delta its binary "
                        + "vertex-to-unordered-edge differential, and k and t natural numbers. "
                        + "If G is k-edge-connected and 2t<k, then any received edge labeling "
                        + "within Hamming distance t of delta(x) has exactly one gradient "
                        + "codeword within distance t. The theorem identifies the edge word, "
                        + "not the vertex labels, which retain a constant ambiguity.")),
                Paragraph(Text(
                    "For two gradient words at distance less than k, delete precisely "
                        + "their disagreement edges. Their number is the Hamming distance. "
                        + "Edge connectivity supplies a walk after deletion between the "
                        + "endpoints of every original edge. Along each surviving edge, the "
                        + "sum of the two vertex labelings is constant. Walking between "
                        + "the endpoints forces the original edge labels to agree. Finally, "
                        + "the Hamming triangle inequality bounds the distance between "
                        + "two candidates by 2t."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula graph = F.Id("G");
        Formula k = F.Id("k");
        Formula t = F.Id("t");
        Formula x = F.Id("x");
        Formula received = F.Id("r");
        Formula c = F.Id("c");
        Formula gradient = Call("edgeDifferential", graph, x);
        return Disp(Seq(
            Call("IsEdgeConnected", graph, k), Sp, Land, Sp,
            D(2), Sp, Times, Sp, t, Sp, Lt, Sp, k, Sp, Land, Sp,
            Call("hammingDist", received, gradient), Sp, Leq, Sp, t,
            Sp, Rightarrow, Sp, Exists, Bang, Sp, c, Comma, Sp,
            c, Sp, InMacro, Sp, Call("range", Call("edgeDifferential", graph)),
            Sp, Land, Sp, Call("hammingDist", received, c), Sp, Leq, Sp, t));
    }
}
