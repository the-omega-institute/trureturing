using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroForcing;

internal sealed class CycleConnectedForcingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ZeroForcing/CycleConnectedForcing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/brimkov2017zeroforcing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The connected forcing polynomial of the cycle C_n is n Σ_{i=2}^{n−1} x^i + x^n for n ≥ 3; the "
        + "cases n ≤ 2 are determined as well.",
        H("Connected forcing polynomial of the cycle"),
        Blocks(
            Describe.Lean(DescribeId.Create("cycle-connected-forcing-sets"),
                DeclarationHandle.Create(Prefix + "connected_forcing_iff"),
                H("Connected forcing sets of the cycle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every n a vertex set S of the cycle C_n on 0, …, n − 1 induces a connected "
                        + "subgraph and is a zero forcing set exactly when S is an arc "
                        + "S = {x : (x − a) mod n < i} for some vertex a and some i ≥ 2, which is the whole "
                        + "cycle once i ≥ n, or n = 2 and S is a single vertex (i = 1).")),
                    Paragraph(Text(
                        "If S misses a vertex v, measure each vertex by its offset (x − (v + 1)) mod n. "
                        + "Adjacent vertices other than v have offsets differing by one, so a walk inside S "
                        + "passes every offset between its ends and S is the arc between its least and "
                        + "greatest offsets. An arc of at least two vertices forces around the cycle: its "
                        + "last vertex has its predecessor black and forces its successor. A single vertex "
                        + "has two distinct white neighbours and forces nothing. On two vertices a single "
                        + "vertex forces the other, which is why single vertices occur for n = 2. This is the "
                        + "counting basis of Proposition 7.8 of B. Brimkov, Graph Coloring, Zero Forcing, "
                        + "and Related Problems (PhD thesis, Rice University, 2017)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cycle-connected-forcing-polynomial"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For n ≥ 3 the number of connected forcing sets of C_n of size i is 1 for i = n, n "
                        + "for 2 ≤ i < n, and 0 otherwise; equivalently Z_c(C_n; x) = n Σ_{i=2}^{n−1} x^i + "
                        + "x^n. For every n the count is 1 for i = n ≠ 0, n for 1 ≤ i < n when i ≥ 2 or "
                        + "n = 2, and 0 otherwise, so Z_c(C_0; x) = 0, Z_c(C_1; x) = x and "
                        + "Z_c(C_2; x) = 2x + x^2.")),
                    Paragraph(Text(
                        "For 2 ≤ i < n the arcs of i vertices are distinct for distinct starting vertices, "
                        + "since the starting vertex is the only member whose predecessor is missing, which "
                        + "gives n of them; the only set of size n is the whole cycle. The source's form "
                        + "n Σ_{i=2}^{n−1} x^i + x^n also holds for n = 1 but not for n = 0, where no set "
                        + "is connected, nor for n = 2, where each single vertex is a connected forcing "
                        + "set. The case n ≥ 3 is Proposition 7.8 of Brimkov (2017)."))),
                DescribeRole.Theorem))));
}
