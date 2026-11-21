using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroForcing;

internal sealed class StarConnectedForcingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ZeroForcing/StarConnectedForcing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/brimkov2017zeroforcing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The connected forcing polynomial of the star K_{1,n−1} is (n − 1)x^{n−1} + x^n for n ≥ 4 "
        + "and equals that of the path P_n for n ≤ 3.",
        H("Connected forcing polynomial of the star"),
        Blocks(
            Describe.Lean(DescribeId.Create("star-graph"),
                DeclarationHandle.Create(Prefix + "starGraph"),
                H("The star"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "The star K_{1,n−1} on the vertices 0, …, n − 1 with centre 0: two distinct "
                        + "vertices are adjacent exactly when one of them is the centre."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("star-connected-forcing-sets"),
                DeclarationHandle.Create(Prefix + "connected_forcing_iff"),
                H("Connected forcing sets of the star"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For n ≥ 1 a vertex set S of K_{1,n−1} induces a connected subgraph and is a zero "
                        + "forcing set exactly when either S contains the centre and misses at most one "
                        + "leaf, or n ≤ 3 and S is a single leaf.")),
                    Paragraph(Text(
                        "Every set containing the centre is connected, and without the centre a connected "
                        + "set is a single leaf. If two leaves are white, every black leaf has only the "
                        + "centre as neighbour and the centre has two white neighbours, so nothing outside "
                        + "S and the centre ever turns black. The centre with at most one white leaf forces "
                        + "that leaf. A single leaf forces the centre, which then forces the last leaf when "
                        + "there are at most two leaves. This is the unit-arm case of the counting in "
                        + "Proposition 7.11 of B. Brimkov, Graph Coloring, Zero Forcing, and Related "
                        + "Problems (PhD thesis, Rice University, 2017)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("star-connected-forcing-polynomial"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For n ≥ 1 the number of connected forcing sets of K_{1,n−1} of size i is "
                        + "[i = n] + (n − 1)[i = n − 1] + (n − 1)[i = 1 and n ≤ 3]. For n ≥ 4 this gives "
                        + "Z_c(K_{1,n−1}; x) = (n − 1)x^{n−1} + x^n, and for every n ≤ 3 the coefficients "
                        + "agree with those of the path P_n, the two smaller nontrivial stars K_{1,1} = P_2 "
                        + "and K_{1,2} ≅ P_3 having the path formulas.")),
                    Paragraph(Text(
                        "The whole vertex set counts once, the n − 1 sets missing one leaf count at size "
                        + "n − 1, and the n − 1 single leaves count at size 1 when n ≤ 3. The general "
                        + "formula needs n ≥ 1: on the empty vertex set no set is connected, while the "
                        + "formula gives 1 at i = 0; the comparison with the path holds for every n ≤ 3, "
                        + "the empty graph included. The case n ≥ 4 is Proposition 7.11 of Brimkov (2017) with "
                        + "every pendant path of one vertex."))),
                DescribeRole.Theorem))));
}
