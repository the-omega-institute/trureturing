using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerStripExpansionCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed colored gap tuples are counted by weak compositions of half the total number of colors.",
        H("Counting the Fixed Gap Tuples"),
        Blocks(
            Node("cigler-strip-expansion-counting-double-gap-lengths", "Expand the half-lengths", "doubleGapLengths",
                "Given a list of natural numbers and a natural remainder r, double every entry and insert a zero between consecutive doubled entries, then add r to the final doubled entry. A singleton a becomes the singleton 2a + r, and the empty list remains empty.", DescribeRole.Definition),
            Node("cigler-strip-expansion-counting-halve-gaps", "Recover the half-lengths", "halveGaps",
                "From a list of colored gaps, retain the lengths of its even-indexed gaps, numbering from zero, and divide each retained length by two with integer division. A singleton gap contributes half its length, and an empty list contributes no entries. The odd-indexed gaps are omitted.", DescribeRole.Definition),
            Node("cigler-strip-expansion-counting-fixed-gap-bijection", "Fixed gaps and weak compositions", "fixed_gap_bijection",
                "For every nonnegative integer j and every Boolean color sequence of length L, the fixed gap tuples with 2j + 1 gaps and that concatenated color sequence are in bijection with the weak compositions of floor(L/2) into j + 1 parts. The forward map takes the half-lengths of the even-indexed gaps. The inverse doubles those parts, inserts zero lengths between them, adds the remainder of L modulo two to the last length, and splits the color sequence at those lengths. For any finite set consisting exactly of all tuples with 2j + 1 gaps and that concatenation, the sum of (-1)^q, where q is the total length of the odd-indexed gaps, is binom(floor(L/2) + j, j).", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
