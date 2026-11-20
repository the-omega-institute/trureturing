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
            Definition("edgeVisit", "Generator incidence",
                AtRank(Bind("e", EdgeType(), Bind("i", GeneratorType(),
                    Seq(Call("edgeVisit", F.Id("e"), F.Id("i")), Colon,
                        Call("Option", Name("Bool")))))),
                "On edge e, the letter e returns true and the letter e+1 returns false. "
                + "Every other letter returns none."),
            Definition("SourceAt", "Source at a generator",
                AtRank(Bind("o", OrientationType(), Bind("i", GeneratorType(),
                    Seq(Call("SourceAt", F.Id("o"), F.Id("i")), Sp, Iff, Sp,
                        Bind("e", EdgeType(), Bind("b", Name("Bool"),
                            Seq(Equal(Call("edgeVisit", F.Id("e"), F.Id("i")),
                                    Call("some", F.Id("b"))), Sp, Implies, Sp,
                                Equal(ApplyOrientation(), F.Id("b"))))))))),
                "For every edge and every Boolean returned by edgeVisit for this generator, "
                + "the orientation of that edge equals the returned Boolean."),
            Definition("flip", "Source flip",
                AtRank(Bind("o", OrientationType(), Bind("i", GeneratorType(),
                    Seq(Call("flip", F.Id("o"), F.Id("i")), Colon, OrientationType())))),
                "Negate the orientation of precisely the incident edges."),
            Definition("Legal", "Legal sequence of source flips",
                AtRank(Bind("o", OrientationType(), Bind("w", WordType(),
                    Seq(Call("Legal", F.Id("o"), F.Id("w")), Colon, Name("Prop"))))),
                "The empty word is legal. A nonempty word requires its first generator to "
                + "be a source and its remaining letters to be legal after the first flip."),
            Definition("Adapted", "Adapted word",
                AtRank(Bind("w", WordType(), Seq(Call("Adapted", F.Id("w")), Sp, Iff, Sp,
                    new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("o"),
                        OrientationType(), Call("Legal", F.Id("o"), F.Id("w")))))),
                "There exists an initial orientation for which the whole word is legal."),
            Describe.Lean(
                DescribeId.Create("frieden-claim"),
                DeclarationHandle.Create(Root + "claim"),
                H("Avoidance and adaptedness in Conjecture 4.10"),
                StatementSource.FromAuthor(Disp(Statement(Equivalent()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 4.10, p. 15. “A reduced word for w₀ ∈ 𝔖ₙ is "
                    + "X-avoiding if and only if it is adapted to an orientation of Aₙ₋₁.” "
                    + "The quantifier ranges over all natural n. Word uses zero-based adjacent "
                    + "generators. AvoidsX uses one-based letters for the retained crossings "
                    + "on each four-element set of labels. Adapted tests for a source before "
                    + "every flip."))),
                DescribeRole.Definition),
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
                Blocks(Paragraph(Text("This proves the named proposition claim. In the converse "
                    + "direction, the last move of a wire at "
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

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("frieden-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Root + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula Statement(Formula conclusion) =>
        AtRank(Bind("w", WordType(), Seq(Call("ReducedReversal", F.Id("w")), Sp, Implies, Sp,
            Parenthesized(conclusion))));

    private static Formula ImpliedAdapted() =>
        Seq(Call("AvoidsX", F.Id("w")), Sp, Implies, Sp, Call("Adapted", F.Id("w")));

    private static Formula Equivalent() =>
        Seq(Call("AvoidsX", F.Id("w")), Sp, Iff, Sp, Call("Adapted", F.Id("w")));

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula AtRank(Formula formula) => Bind("n", Seq(Mathbb, Grp(F.Id("N"))), formula);
    private static Formula Bind(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula WordType() => Call("Word", F.Id("n"));
    private static Formula OrientationType() => Call("Orientation", F.Id("n"));
    private static Formula GeneratorType() => Call("Fin", Seq(F.Id("n"), Minus, D(1)));
    private static Formula EdgeType() => Call("Fin", Seq(F.Id("n"), Minus, D(2)));
    private static Formula ApplyOrientation() => new Formula.Apply(F.Id("o"), [F.Id("e")]);
    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Name(name), [.. args]);
}
