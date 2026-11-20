using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroForcing;

internal sealed class CycleConnectedForcingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ZeroForcing/CycleConnectedForcing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/brimkov2017zeroforcing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The connected forcing polynomial of the cycle C_n is n Σ_{i=2}^{n−1} x^i + x^n for n = 1 and "
        + "every n ≥ 3.",
        H("Connected forcing polynomial of the cycle"),
        Blocks(
            Describe.Lean(DescribeId.Create("cycle-connected-forcing-sets"),
                DeclarationHandle.Create(Prefix + "connected_forcing_iff"),
                H("Connected forcing sets of the cycle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every n ≠ 2 a vertex set S of the cycle C_n on 0, …, n − 1 induces a connected "
                        + "subgraph and is a zero forcing set exactly when S is an arc of at least two "
                        + "vertices: S = {x : (x − a) mod n < i} for some vertex a and some i ≥ 2, which is "
                        + "the whole cycle once i ≥ n.")),
                    Paragraph(Text(
                        "If S misses a vertex v, measure each vertex by its offset (x − (v + 1)) mod n. "
                        + "Adjacent vertices other than v have offsets differing by one, so a walk inside S "
                        + "passes every offset between its ends and S is the arc between its least and "
                        + "greatest offsets. An arc of at least two vertices forces around the cycle: its "
                        + "last vertex has its predecessor black and forces its successor. A single vertex "
                        + "has two distinct white neighbours and forces nothing. On two vertices a single "
                        + "vertex forces the other, so the characterization fails for n = 2. This is the "
                        + "counting basis of Proposition 7.8 of B. Brimkov, Graph Coloring, Zero Forcing, "
                        + "and Related Problems (PhD thesis, Rice University, 2017)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cycle-connected-forcing-polynomial"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For n = 1 and every n ≥ 3 the number of connected forcing sets of C_n of size i is 1 "
                        + "for i = n, n for 2 ≤ i < n, and 0 otherwise. Equivalently "
                        + "Z_c(C_n; x) = n Σ_{i=2}^{n−1} x^i + x^n.")),
                    Paragraph(Text(
                        "For 2 ≤ i < n the arcs of i vertices are distinct for distinct starting vertices, "
                        + "since the starting vertex is the only member whose predecessor is missing, which "
                        + "gives n of them; the only set of size n is the whole cycle. The hypotheses are "
                        + "sharp: on the empty vertex set no set is connected, while the formula gives 1 at "
                        + "i = 0, and on two vertices each single vertex is a connected forcing set. The "
                        + "case n ≥ 3 is Proposition 7.8 of Brimkov (2017)."))),
                DescribeRole.Theorem))));
}
