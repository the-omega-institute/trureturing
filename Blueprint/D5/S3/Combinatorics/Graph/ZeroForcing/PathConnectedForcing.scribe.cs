using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroForcing;

internal sealed class PathConnectedForcingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ZeroForcing/PathConnectedForcing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/brimkov2017zeroforcing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The connected forcing polynomial of the path P_n is 2x + Σ_{i=2}^n (n − i + 1) x^i.",
        H("Connected forcing polynomial of the path"),
        Blocks(
            Describe.Lean(DescribeId.Create("path-connected-forcing-sets"),
                DeclarationHandle.Create(Prefix + "connected_forcing_iff"),
                H("Connected forcing sets of the path"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For n ≥ 2 a vertex set S of the path P_n on 0, …, n − 1 induces a connected subgraph "
                        + "and is a zero forcing set exactly when S is an interval [a, b] with a < b, or S is "
                        + "one of the two end vertices.")),
                    Paragraph(Text(
                        "A walk in the induced subgraph moves by one step at a time, so it passes every "
                        + "intermediate vertex and a connected S is an interval. An interval with at least two "
                        + "vertices forces outward: its right end has its left neighbour black and forces "
                        + "the next vertex, and symmetrically on the left. An end vertex forces its unique "
                        + "neighbour and then the pair forces the path. An interior vertex alone has two "
                        + "white neighbours and forces nothing. The characterization is the counting basis of "
                        + "Proposition 7.7 of B. Brimkov, Graph Coloring, Zero Forcing, and Related Problems "
                        + "(PhD thesis, Rice University, 2017)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("path-connected-forcing-polynomial"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For n ≥ 2 the number of connected forcing sets of P_n of size i is 0 for i = 0, 2 "
                        + "for i = 1, and n + 1 − i for every i ≥ 2 (which is 0 for i > n). Equivalently "
                        + "Z_c(P_n; x) = 2x + Σ_{i=2}^n (n − i + 1) x^i.")),
                    Paragraph(Text(
                        "The empty set is not connected. The size-one sets are the two end vertices. An "
                        + "interval of size i ≥ 2 is determined by its left end a with a + i ≤ n, giving "
                        + "n + 1 − i of them. This is Proposition 7.7 of Brimkov (2017)."))),
                DescribeRole.Theorem))));
}
