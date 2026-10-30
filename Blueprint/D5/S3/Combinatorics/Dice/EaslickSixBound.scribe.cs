using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Dice;

internal sealed class EaslickSixBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Dice/EaslickSixBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/easlick2026minimaldice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete dice conjecture follows from an exhaustive six-face upper bound and uniform longer cycles.",
        H("EaslickSixBound"),
        Blocks(
            Node("easlick-six-cycle-bound", "The global six-face upper bound", "six_cycle_bound",
                "For every natural k, HasCycle(6,k) implies k at most six. A complete recursive enumeration includes all 462 sorted six-face dice with labels from one through six, including repetitions and the standard die. Every score-19 edge weakly decreases the certified rank. A closed cycle therefore has one rank and lies in its entire rank fiber. All fibers have at most seven elements. In each seven-element fiber, two distinct vertices have the same unique internal successor. A seven-cycle would exhaust that fiber, contradicting injectivity of the cyclic successor operation on distinct vertices. The certificate is checked by Lean kernel reduction; its rank data are a witness, never an assumed law."),
            Node("easlick-s-six", "The attained six-face maximum", "S_six",
                "S(6) holds: an explicit six-cycle attains the global upper bound of six. The upper bound applies to every simple directed cycle in the full graph at the true least attainable strict-win probability above one half."),
            Node("easlick-conjecture-one", "The complete Easlick conjecture", "conjecture_one",
                "The complete proposition is S(6) and, for every natural n at least seven, not S(n). Natural n faithfully represents the source integer range n at least three. Dice are all nondecreasing lists of n labels in the interval from one through n. Repeated faces and the standard tuple remain included. Strict-win probability is unconditional on the uniform independent product of face indices. The attained minimum is proved, not taken from the author parity formula. S quantifies over all longer simple cycles, with no finite cutoff.")
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
