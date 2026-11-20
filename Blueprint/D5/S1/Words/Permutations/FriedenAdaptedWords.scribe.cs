using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class FriedenAdaptedWordsDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/FriedenAdaptedWords.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/frieden2026bigcactus");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-wire avoidance and source-flip adaptedness in arbitrary rank.",
        H("Four-wire avoidance characterizes adaptedness"),
        Blocks(
            Paragraph(Text("An orientation assigns a direction to every edge between two "
                + "consecutive generators. A generator is legal when all its incident edges "
                + "point away from it. Using it reverses precisely those edges.")),
            Describe.Lean(
                DescribeId.Create("frieden-avoidance-implies-adapted"),
                DeclarationHandle.Create(Root + "avoidance_implies_adapted"),
                H("The avoidance-to-adaptedness implication of Conjecture 4.10"),
                StatementSource.FromAuthor(Disp(Statement(ImpliedAdapted()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For each natural n and each word on the n-1 adjacent "
                    + "generators, suppose its length is n(n-1)/2 and its chronological swaps "
                    + "send the identity to the reversal. Suppose also that restricting to "
                    + "any four labels gives a word outside X, whose elements are 123212, "
                    + "321232, 212321 and 232123. Then there exists an initial path orientation "
                    + "in which the entire word is a legal sequence of source flips. "
                    + "Each two-generator projection must alternate because a repetition would "
                    + "force one of the four restrictions, with reflection exchanging the two "
                    + "ends of the edge. The first letter in each projection determines the "
                    + "edge direction needed for the sequence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("frieden-conjecture-410"),
                DeclarationHandle.Create(Root + "conjecture410"),
                H("Conjecture 4.10"),
                StatementSource.FromAuthor(Disp(Statement(Equivalent()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("In the converse direction, the last move of a wire at "
                    + "an interior position leaves an incident arrow blocking a return. Thus "
                    + "a turn is possible only at an endpoint. Two turns would require crossing "
                    + "the entire network between moves into and out of its endpoints. This "
                    + "would exceed the n-1 moves available to a wire, since it crosses each "
                    + "other label once. Restriction retains a subsequence of the moves of "
                    + "each selected wire, with their directions preserved. Each word in X "
                    + "contains a wire whose retained directions alternate twice."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("frieden-2026-adapted-reversal-words"),
                    ResolutionKind.Proved)))));

    private static Formula Statement(Formula conclusion) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            Seq(Mathbb, Grp(F.Id("N"))),
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("w"),
                Call("Word", F.Id("n")),
                Seq(Call("ReducedReversal", F.Id("w")), Sp, Implies, Sp, Open, conclusion, Close)));

    private static Formula ImpliedAdapted() =>
        Seq(Call("AvoidsX", F.Id("w")), Sp, Implies, Sp, Call("Adapted", F.Id("w")));

    private static Formula Equivalent() =>
        Seq(Call("AvoidsX", F.Id("w")), Sp, Iff, Sp, Call("Adapted", F.Id("w")));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
