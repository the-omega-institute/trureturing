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
            PublishedNode("scatteredCount_eq_count_sublistsLen", Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Colon, Sp, PublishedName("Type"))), Comma, Sp, Parenthesized(Seq(OpenBracket, Seq(PublishedName("DecidableEq"), Sp, F.Id("A")), CloseBracket, Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(PublishedName("pattern"), Colon, Sp, Seq(PublishedName("List"), Sp, F.Id("A")))), Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(PublishedName("source"), Colon, Sp, Seq(PublishedName("List"), Sp, F.Id("A")))), Comma, Sp, Parenthesized(Seq(PublishedName("scatteredCount"), Sp, PublishedName("pattern"), Sp, PublishedName("source"), Sp, Eq, Sp, Parenthesized(Seq(Seq(PublishedName("source"), Dot, PublishedName("sublistsLen")), Sp, Seq(PublishedName("pattern"), Dot, PublishedName("length")))), Sp, Dot, Sp, PublishedName("count"), Sp, PublishedName("pattern"))))))))))), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
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
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration) => declaration switch
    {
        "exactKDeck" => Seq(Forall, Sp, F.Id("k"), Comma, F.Id("source"),
            Comma, F.Id("pattern"), Comma, Call("length", F.Id("pattern")),
            Eq, Sp, F.Id("k"), Rightarrow,
            Equal(Call("exactKDeck", F.Id("k"), F.Id("source"), F.Id("pattern")),
                Call("scatteredCount", F.Id("pattern"), F.Id("source")))),
        "exactKDeckImage" => Seq(Forall, Sp, F.Id("A"), Comma, F.Id("k"),
            Comma, F.Id("n"), Comma, Sp,
            Equal(Call("exactKDeckImage", F.Id("A"), F.Id("k"), F.Id("n")),
                Call("image", Call("exactKDeck", F.Id("k")),
                    Call("wordsOfLength", F.Id("A"), F.Id("n"))))),
        "scatteredCount_eq_of_exactKDeck_eq" => Seq(Forall, Sp,
            F.Id("k"), Comma, F.Id("n"), Comma, F.Id("left"), Comma,
            F.Id("right"), Comma, F.Id("pattern"), Comma, Sp,
            Equal(Call("length", F.Id("left")), F.Id("n")), Land,
            Equal(Call("length", F.Id("right")), F.Id("n")), Land,
            Sp, F.Id("k"), Leq, Sp, F.Id("n"), Land,
            Call("length", F.Id("pattern")), Leq, Sp, F.Id("k"), Land,
            Equal(Call("exactKDeck", F.Id("k"), F.Id("left")),
                Call("exactKDeck", F.Id("k"), F.Id("right"))), Rightarrow,
            Equal(Call("scatteredCount", F.Id("pattern"), F.Id("left")),
                Call("scatteredCount", F.Id("pattern"), F.Id("right")))),
        "exactKDeck_eq_iff_cutoffMagnus_eq_of_common_length" => Seq(Forall, Sp,
            F.Id("k"), Comma, F.Id("n"), Comma, F.Id("left"), Comma,
            F.Id("right"), Comma, Sp,
            Equal(Call("length", F.Id("left")), F.Id("n")), Land,
            Equal(Call("length", F.Id("right")), F.Id("n")), Land,
            Sp, F.Id("k"), Leq, Sp, F.Id("n"), Rightarrow,
            Equal(Call("exactKDeck", F.Id("k"), F.Id("left")),
                Call("exactKDeck", F.Id("k"), F.Id("right"))), Iff,
            Equal(Call("cutoffMagnus", F.Id("k"), F.Id("left")),
                Call("cutoffMagnus", F.Id("k"), F.Id("right")))),
        _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
    };

    private static DocumentBlock PublishedNode(string name, Formula formula, DescribeRole role,
        AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("singhvi-owner-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore." + name), H(name), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text("The formula relates a word's constant runs and its scattered-subword counts."))), role);
    private static Formula PublishedName(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
