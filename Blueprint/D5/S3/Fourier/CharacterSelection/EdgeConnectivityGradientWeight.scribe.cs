using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class EdgeConnectivityGradientWeightDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Fourier/CharacterSelection/EdgeConnectivityGradientWeight."
            + "edge_connected_iff_gradient_weight";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Edge connectivity is characterized by the weight of every nonconstant binary edge gradient.",
        H("Edge Connectivity and Binary Gradient Weight"),
        Blocks(Describe.Lean(
            DescribeId.Create("edge-connected-iff-gradient-weight"),
            DeclarationHandle.Create(Declaration),
            H("Edge connectivity from binary gradients"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be any simple graph with finitely many edges, k any natural number, "
                        + "and delta the binary vertex-to-edge differential. G is k-edge-connected "
                        + "exactly when every vertex labeling that differs at two vertices has "
                        + "edge word delta(x) of Hamming weight at least k. No connectedness or "
                        + "finiteness assumption on vertices is required. The statement concerns "
                        + "edge words, not uniqueness of vertex labels.")),
                Paragraph(Text(
                    "For the forward direction, delete the edges supporting a gradient of weight "
                        + "less than k. A surviving walk between vertices with different labels "
                        + "would force those labels to agree. Conversely, if deleting fewer than k "
                        + "edges separates u from v, label each vertex by membership in the "
                        + "component reachable from u after deletion. This nonconstant labeling "
                        + "has zero gradient on every surviving edge, so its gradient support is "
                        + "contained in the deletion set and has weight less than k."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) result.AddRange([Comma, Sp]);
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }

    private static Formula TheoremFormula()
    {
        Formula graph = F.Id("G"), k = F.Id("k"), x = F.Id("x");
        Formula u = F.Id("u"), v = F.Id("v");
        Formula nonconstant = Seq(Exists, Sp, u, Comma, Sp, v, Comma, Sp,
            Call("x", u), Sp, Neq, Sp, Call("x", v));
        return Disp(Seq(
            Call("IsEdgeConnected", graph, k), Sp, Iff, Sp,
            Forall, Sp, x, Comma, Sp,
            Grp(nonconstant), Sp, Rightarrow, Sp,
            k, Sp, Leq, Sp, Call("hammingNorm", Call("edgeDifferential", graph, x))));
    }
}
