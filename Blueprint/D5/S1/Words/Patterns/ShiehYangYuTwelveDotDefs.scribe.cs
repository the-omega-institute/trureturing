using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class ShiehYangYuTwelveDotDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/ShiehYangYuTwelveDotDefs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/yangshiehyu2025dotted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Peak-run reversal followed by West's stack map defines the 12-dot machine and its sortable permutations.",
        H("The Shieh-Yang-Yu 12-Dot Machine"),
        Blocks(
            Node("syy-twelve-dot-peak-runs-definition", "Peak runs", "peakRuns",
                "For a word of natural numbers, the empty word has no peak runs. For a nonempty "
                + "word beginning with v, the first run consists of v followed by the longest "
                + "initial segment of the remaining word whose entries are at most v. The "
                + "remaining runs are obtained by applying the same rule to the remaining suffix. "
                + "On permutations, each run begins at a left-to-right maximum and ends immediately "
                + "before the next left-to-right maximum, as in Section 2 of the cited paper.",
                DescribeRole.Definition),
            Node("syy-twelve-dot-reversal-definition", "Reverse each peak run", "s12",
                "The map s12 reverses each peak run and concatenates the reversed runs in their "
                + "original order. Proposition 3.1 of the cited paper identifies this operation "
                + "on permutations with the stack map avoiding the dotted pattern 12-dot. "
                + "Peak-run reversal is the definition of s12 for all words of natural numbers.",
                DescribeRole.Definition),
            Node("syy-twelve-dot-sortable-definition", "Machine-sortable permutations", "sortable",
                "For a natural number n, sortable(n) is the set of permutations of the word "
                + "[1,...,n] for which applying s12 and then West's stack map gives [1,...,n]. "
                + "West's map pops the stack while its top is smaller than the next input, "
                + "pushes that input otherwise, and flushes the remaining stack when the input "
                + "is empty. Sortability requires a single application of this composition.",
                DescribeRole.Definition),
            Node("syy-twelve-dot-claim-definition", "The central binomial assertion", "claim",
                "The proposition claim states that, for every natural number n at least one, "
                + "the number of elements of sortable(n) is the binomial coefficient choosing "
                + "n minus one from 2n minus two. This is Conjecture 6.1 of the cited paper, "
                + "with the first stack map expressed by peak-run reversal.",
                DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
