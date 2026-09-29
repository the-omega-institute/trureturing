using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicTetranacciPatternsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avoidance of 1324 constrains the relative order of high and low arcs.",
        H("Pattern Constraints on Cycle Arcs"),
        Blocks(
            Node("archer-cyclic-suffix-213", "No 213 in the rooted suffix", "rooted_suffix_avoids_213",
                "If a word beginning with one avoids 1324 and its remaining letters exceed one, that suffix contains no 213 subsequence.", DescribeRole.Theorem),
            Node("archer-cyclic-high-above-low", "Separation of the arcs", "high_arc_above_low_arc",
                "In a 1324-avoiding word beginning with one, every letter before two exceeds every letter after two when the prefix letters exceed two and all letters are distinct.", DescribeRole.Theorem),
            Node("archer-cyclic-low-increasing", "Increasing low arc", "low_arc_has_no_descent",
                "If every rotation avoids 1324 and the letters after two lie below a nonempty high prefix, then the letters after two have no descent.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
