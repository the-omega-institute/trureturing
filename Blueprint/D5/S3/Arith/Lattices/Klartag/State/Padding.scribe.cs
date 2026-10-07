using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class PaddingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/Padding.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("Padding"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate padding to the stochastic ellipsoid construction.")),
            Node("claim-1", "padSum", "pad Sum",
                "The accumulated padding P_k = ∑_{i<k} c_i(ω₁)·η_i.", DescribeRole.Definition),
            Node("claim-2", "paddedProc", "padded Proc",
                "The padded process S̃_k = (M_k − M₀) + P_k.", DescribeRole.Definition),
            Node("claim-3", "negPad", "neg Pad",
                "Negate every padding coordinate, leaving the chain alone.", DescribeRole.Definition),
            Node("claim-7", "padSum_negPad", "pad Sum neg Pad",
                "The accumulated padding is odd in the padding coordinates.", DescribeRole.Theorem),
            Node("claim-8", "measurePreserving_negPad", "measure Preserving neg Pad",
                "negPad is measure preserving when the padding law is symmetric.", DescribeRole.Theorem),
            Node("claim-10", "hitSet", "hit Set",
                "{∃ k ≤ N, M_k ≤ 0} — the chain reaches the boundary. Depends only on the chain.", DescribeRole.Definition),
            Node("claim-11", "levSet", "lev Set",
                "{∃ k ≤ N, S̃_k ≤ −M₀} — the padded process reaches −M₀.", DescribeRole.Definition),
            Node("claim-12", "hsym_of_symmetric", "hsym of symmetric",
                "hsym: the padded process reaches −M₀ with at least half the probability that the chain reaches the boundary. P(∃ k ≤ N, M_k ≤ 0) ≤ 2 · P(∃ k ≤ N, S̃_k ≤ −M₀). This is the first of the two factors of 2 in padded_increment_tail's constant 4. It needs only that the padding law is symmetric; the chain M is completely arbitrary.", DescribeRole.Theorem),
            Node("claim-15", "map_finsetSum_gaussian", "map finset Sum gaussian",
                "The sum over a Finset of i.i.d. centred Gaussian coordinates is centred Gaussian.", DescribeRole.Theorem),
            Node("claim-16", "map_walkSum_gaussian", "map walk Sum gaussian",
                "The terminal law. The walk's final value under i.i.d. N(0,δ) increments is N(0, N·δ).", DescribeRole.Theorem),
            Node("claim-17", "hlaw_of_hincl", "hlaw of hincl",
                "hlaw from hincl. If the increment vector is i.i.d. N(0,δ), the terminal value is N(0, N·δ) — so padded_tail_assembled's last premise is free.", DescribeRole.Theorem),
            Node("claim-18", "measurePreserving_neg_gaussianReal", "measure Preserving neg gaussian Real",
                "A centred real Gaussian is symmetric.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
