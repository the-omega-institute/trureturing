using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Parking;

internal sealed class MaximumLetterGapsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Parking/MaximumLetterGaps.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Parking/alexandersson2026parking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deletion of the maximum letter gives an ordered gap profile and a shorter bounded parking word.",
        H("Maximum-letter gaps in bounded parking words"),
        Blocks(
            Node("RankBound", "The sorted rank test", DescribeRole.Definition,
                "At every zero-based index i, the letter at i is at most i + 1."),
            Node("BoundedParking", "Bounded parking words", DescribeRole.Definition,
                "The word has length n, each letter is in 1 through m, and sorting the word in ascending order satisfies the rank test."),
            Node("Original", "The maximum-letter fiber", DescribeRole.Definition,
                "A bounded parking word at length n and bound m whose letter m occurs exactly r times."),
            Node("Retained", "The retained word and its profile", DescribeRole.Definition,
                "A bounded parking word at length n − r and bound m − 1 together with an ordered list of n − r + 1 nonnegative gap sizes summing to r."),
            Node("sorted_prefix_membership", "The rank test through gap insertion", DescribeRole.Theorem,
                "For 2 ≤ m ≤ n and 1 ≤ r ≤ n − m + 1, insert a total of r copies of m into the ordered gaps of a word of length n − r with letters strictly below m. The reconstructed word is bounded parking exactly when the retained word passes the shorter test. In sorted order the added letters form a final constant block, and its first rank is n − r + 1."),
            Node("max_count_cut", "Maximum-letter multiplicity cutoff", DescribeRole.Theorem,
                "In a bounded parking word with m ≤ n, at most n − m + 1 letters equal m. If m occurs, its first sorted occurrence has rank n − r + 1 for multiplicity r."),
            Node("delete", "Delete the maximum letters", DescribeRole.Definition,
                "Scan the actual word to keep its nonmaximum letters and count copies of m in each gap, including both ordered boundary gaps."),
            Node("insert", "Reconstruct from the gap profile", DescribeRole.Definition,
                "Put the specified number of copies of m into each of the ordered gaps. The sorted-prefix equivalence proves membership in the maximum-letter fiber."),
            Node("parkingGapEquiv", "The deletion and insertion equivalence", DescribeRole.Definition,
                "The two operations are inverse for each admissible n, m and positive r. The replay law for unary gaps recovers the original word, and reading the profile of a reconstructed word recovers the retained word and every gap size.")),
        []));

    private static DocumentBlock Node(
        string declaration, string title, DescribeRole role, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("maximumlettergaps-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),
            role, resolution);
}
