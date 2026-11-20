using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroForcing;

internal sealed class SpiderConnectedForcingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ZeroForcing/SpiderConnectedForcing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/brimkov2017zeroforcing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For k ≥ 3 arms of lengths h_j ≥ 1 the spider S(h_1, …, h_k) has connected forcing polynomial "
        + "x^k (x ∏_j F_{h_j} + Σ_j ∏_{t≠j} F_{h_t}), where F_h = 1 + x + ⋯ + x^{h−1}.",
        H("Connected forcing polynomial of the spider"),
        Blocks(
            Describe.Lean(DescribeId.Create("spider-graph"),
                DeclarationHandle.Create(Prefix + "spider"),
                H("The spider"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "The spider S(h_1, …, h_k) has a centre and k pendant paths, the arms, the jth "
                        + "with h_j vertices. Its vertices are the centre and the pairs (j, p) with "
                        + "p < h_j, the vertex of arm j at distance p + 1 from the centre; the centre is "
                        + "adjacent to each (j, 0) and (j, p) is adjacent to (j, p + 1)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("spider-body"),
                DeclarationHandle.Create(Prefix + "body"),
                H("Centre and initial arm segments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a tuple ℓ of natural numbers, body ℓ is the set made of the centre and the "
                        + "first ℓ_j vertices of each arm j."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("spider-connected-forcing-sets"),
                DeclarationHandle.Create(Prefix + "connected_forcing_iff"),
                H("Connected forcing sets of the spider"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For k ≥ 3 arms of positive lengths, a vertex set induces a connected subgraph and "
                        + "is a zero forcing set exactly when it is body ℓ for a tuple with ℓ_j ≤ h_j for "
                        + "every arm and ℓ_j = 0 for at most one arm.")),
                    Paragraph(Text(
                        "A walk leaving a region of the graph passes through the only vertex joining the "
                        + "region to the rest. Hence a connected set without the centre lies in one arm, "
                        + "and a connected set containing the centre meets each arm in an initial "
                        + "segment. A set inside one arm forces nothing beyond that arm and the centre, "
                        + "because the centre then has two white neighbours in other arms. If two arms "
                        + "are untouched, the centre always keeps two white neighbours there. With at "
                        + "most one untouched arm, every touched arm forces outward along itself and the "
                        + "centre then forces the remaining arm. This is the characterization in the "
                        + "proof of Proposition 7.11 of B. Brimkov, Graph Coloring, Zero Forcing, and "
                        + "Related Problems (PhD thesis, Rice University, 2017)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spider-connected-forcing-polynomial"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For k ≥ 3 arms of lengths h_j ≥ 1, the number of connected forcing sets of the "
                        + "spider of size i is the coefficient of x^i in "
                        + "x^k (x ∏_j F_{h_j} + Σ_j ∏_{t≠j} F_{h_t}), with F_h = Σ_{e<h} x^e.")),
                    Paragraph(Text(
                        "The set body ℓ has 1 + Σ_j ℓ_j vertices, and distinct tuples give distinct sets. "
                        + "Summing x^{1+Σℓ_j} over the tuples touching every arm gives "
                        + "x ∏_j (x + ⋯ + x^{h_j}) = x^{k+1} ∏_j F_{h_j}; over the tuples leaving exactly "
                        + "arm j untouched it gives x ∏_{t≠j} (x F_{h_t}) = x^k ∏_{t≠j} F_{h_t}. This is "
                        + "Proposition 7.11 of Brimkov (2017), whose coefficient of x^j counts the "
                        + "compositions s(j − 1; h_1, …, h_k) and s(j − 1; h_1, …, h_{ℓ−1}, h_{ℓ+1}, …, "
                        + "h_k). The hypotheses are needed: with two arms the spider is a path, whose end "
                        + "vertices are connected forcing sets of size 1 while the formula has no x term; with "
                        + "an arm j of length 0 the graph is the spider on the other arms, while the "
                        + "formula becomes x^k ∏_{t≠j} F_{h_t}, which counts only the sets touching every "
                        + "other arm."))),
                DescribeRole.Theorem))));
}
