using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ExactDecks.Growth;

internal sealed class ExactDecksGrowthExactDeckCoreDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact fixed-length decks recover every shorter scattered count.",
        H("ExactDeckCore"),
        Blocks(
            Paragraph(Text(
                "The exact-deck objects formalize the source paper's actual vectors of all "
                + "length-k scattered-subword counts. The repository bridge first proves that, "
                + "at a common source length, exact k-deck equality recovers every shorter count "
                + "and is equivalent to equality of the full cutoff Magnus vector.")),
            D("exact-k-deck", "exactKDeck", "An actual exact k-deck",
                "For finite A, exactKDeck k source is the function sending each actual pattern of length exactly k to its scatteredCount in source.", DescribeRole.Definition, true),
            D("exact-k-deck-image", "exactKDeckImage", "Decks realized at one source length",
                "exactKDeckImage A k n is the finite image of exactKDeck k on all actual words over A of length exactly n.", DescribeRole.Definition, true),
            D("short-counts-from-exact-deck", "scatteredCount_eq_of_exactKDeck_eq", "Exact decks recover all shorter counts",
                "For finite A with decidable equality, common length n, k<=n, and a pattern of length at most k, equality of exactKDeck k for the two source words implies equality of that pattern's scattered counts."),
            D("exact-deck-iff-cutoff", "exactKDeck_eq_iff_cutoffMagnus_eq_of_common_length", "Exact-deck and cutoff equality coincide",
                "For finite A, source words of the same length n, and k<=n, equality of their actual exact k-decks is equivalent to equality of cutoffMagnus k."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
