using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming;

internal sealed class HammingMultipartitePartitionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Hamming/ahmedkunjwal2026quasiprocess");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every mixed-alphabet Hamming graph in at least four dimensions admits a partition "
            + "into maximal full coordinate lines using every direction.",
        H("All-direction partitions of mixed-alphabet Hamming graphs"),
        Blocks(
            Node("hamming-vertices", "Mixed vertices", "Vertex",
                "For each coordinate i in Fin n, the vertex independently chooses an element "
                    + "of Fin (d i). Alphabet sizes may differ.", DescribeRole.Definition),
            Node("hamming-graph", "Hamming adjacency", "graph",
                "Vertices are adjacent exactly when they disagree in one coordinate and "
                    + "agree in every other coordinate.", DescribeRole.Definition),
            Node("hamming-line", "Full coordinate lines", "line",
                "The full line in direction i through x fixes x in every coordinate except i. "
                    + "The coordinate i ranges over its entire alphabet.", DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hamming-multipartite-partition"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Ahmed–Kunjwal Conjecture V.1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every natural n at least four and every independent alphabet-size "
                            + "function d with d(i) at least two, there is a family P of nonempty "
                            + "sets of vertices. Every vertex belongs to exactly one member. "
                            + "Every member is a full coordinate line and an inclusion-maximal "
                            + "clique of the Hamming graph. Every coordinate i is the direction "
                            + "of some full line in P.")),
                    Paragraph(Text(
                        "A private four-dimensional binary selector is checked by kernel "
                            + "reduction. Its selected coordinate is stable under flipping that "
                            + "coordinate. Induction adds a coordinate by replacing one binary "
                            + "edge with vertical edges; a second edge in the distinguished "
                            + "direction supplies the next two reserves. Every other direction "
                            + "survives because its selector value differs.")),
                    Paragraph(Text(
                        "For mixed alphabets, zero maps to false and every positive symbol maps "
                            + "to true. The binary selector is constant along the entire selected "
                            + "mixed line, including all positive symbols. Fixing the actual "
                            + "off-direction coordinates splits each binary edge preimage into "
                            + "full lines. Constancy gives unique family membership. An outsider "
                            + "disagrees off the direction, and a line point can also disagree "
                            + "in the direction, proving inclusion-maximality.")),
                    Paragraph(Text(
                        "The source attributes the binary case to Erde; that case is not "
                            + "claimed as new. The physics interpretation, optimal counts, and "
                            + "exhaustive literature priority are not formalized. This is an "
                            + "original Apache-2.0 Lean implementation by OpenAI Codex (GPT-6), "
                            + "using the pinned Mathlib APIs. Independent review, repository "
                            + "admission, and required CI remain separate gates."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ahmed-kunjwal-2026-hamming-multipartite-partition"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
