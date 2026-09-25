using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ExactDecks.Growth;

internal sealed class ExactDecksGrowthExactDeckLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckLowerBound";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-length padding loses exactly one degree in the exact-deck lower bound.",
        H("ExactDeckLowerBound"),
        Blocks(
            Paragraph(Text(
                "The exact-deck objects formalize the source paper's actual vectors of all "
                + "length-k scattered-subword counts. The repository bridge first proves that, "
                + "at a common source length, exact k-deck equality recovers every shorter count "
                + "and is equivalent to equality of the full cutoff Magnus vector.")),
            D("actual-exact-deck-lower-bound", "actual_exactKDeckImage_weightedLyndon_lower_bound", "Weighted-Lyndon lower growth for exact decks",
                "For every finite linearly ordered A with at least two letters and every k>=1, there are naturals C,N with 0<C such that for all n>=N, n^(weightedLyndonExponent A k-1) <= C*(exactKDeckImage A k n).card. Padding turns a ball representative into a word of exact length n while retaining an injective deck encoding."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
