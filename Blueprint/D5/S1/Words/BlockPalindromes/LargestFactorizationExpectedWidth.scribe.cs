using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BlockPalindromes;

internal sealed class LargestFactorizationExpectedWidthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/gabricshallit2023blockpalindromes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The expected largest block-palindrome width converges to the A274199 series.",
        H("LargestFactorizationExpectedWidth"), Blocks(
            Node("bpal-tailprobability", "tailProbability",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("r"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("tailProbability"), Sp, FormulaDsl.Id("k"), Sp, FormulaDsl.Id("n"), Sp, FormulaDsl.Id("r"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Const("tailWords"), Sp, FormulaDsl.Id("k"), Sp, FormulaDsl.Id("n"), Sp, FormulaDsl.Id("r"))), Sp, Dot, Sp, Const("card"), Sp, Colon, Sp, R())), Sp, Slash, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, R())), Sp, Seq(Caret, Grp(FormulaDsl.Id("n"))))),
                "The defining expression of tailProbability.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("bpal-renewal-tail-limit", "renewal_tail_limit",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, FormulaDsl.Id("k"))), Sp, Rightarrow, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("r"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("Tendsto"), Sp, Parenthesized(Seq(Const("fun"), Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, Colon, Sp, N())), Sp, Mapsto, Sp, Const("tailProbability"), Sp, FormulaDsl.Id("k"), Sp, FormulaDsl.Id("n"), Sp, FormulaDsl.Id("r"))), Sp, Const("atTop"), Sp, Parenthesized(Seq(Const("nhds"), Sp, Parenthesized(Seq(Parenthesized(Seq(FormulaDsl.Id("q"), Sp, FormulaDsl.Id("k"), Sp, Parenthesized(Seq(Const("uCount"), Sp, FormulaDsl.Id("k"))))), Sp, Seq(Caret, Grp(FormulaDsl.Id("r"))))))))))),
                "The exact renewal recursion, summability of its coefficients, and dominated convergence give the r-th power of the unbordered-word mass as the limit.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bpal-peelcentre", "peelCentre",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("alpha"), Sp, Colon, Sp, Const("Type"))), Sp, Parenthesized(Seq(FormulaDsl.Id("w"), Sp, Colon, Sp, Const("List"), Sp, FormulaDsl.Id("alpha"))), Sp, Comma, Sp, Const("peelCentre"), Sp, FormulaDsl.Id("w"), Sp, Eq, Sp, Const("if"), Sp, FormulaDsl.Id("hw"), Sp, Colon, Sp, Exists, Sp, Parenthesized(Seq(FormulaDsl.Id("b"), Sp, Colon, Sp, Const("List"), Sp, FormulaDsl.Id("alpha"))), Sp, Comma, Sp, Const("IsBorder"), Sp, FormulaDsl.Id("w"), Sp, FormulaDsl.Id("b"), Sp, Const("then"), Sp, Const("peelCentre"), Sp, Parenthesized(Seq(Const("peeledCore"), Sp, FormulaDsl.Id("w"), Sp, FormulaDsl.Id("hw"))), Sp, Const("else"), Sp, FormulaDsl.Id("w"))),
                "The defining expression of peelCentre.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("bpal-emptywords", "emptyWords",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("emptyWords"), Sp, FormulaDsl.Id("k"), Sp, FormulaDsl.Id("n"), Sp, Eq, Sp, Parenthesized(Parenthesized(Seq(Const("DepthBudgetIidGreedyOptimality"), Sp, Dot, Sp, Const("words"), Sp, FormulaDsl.Id("n"), Sp, Colon, Sp, Const("Finset"), Sp, Parenthesized(Seq(Const("List"), Sp, Parenthesized(Seq(Const("Fin"), Sp, FormulaDsl.Id("k")))))))), Sp, Dot, Sp, Const("filter"), Sp, Parenthesized(Seq(Const("fun"), Sp, FormulaDsl.Id("w"), Sp, Mapsto, Sp, Const("peelCentre"), Sp, FormulaDsl.Id("w"), Sp, Eq, Sp, OpenBracket, Sp, CloseBracket)))),
                "The defining expression of emptyWords.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("bpal-emptyprobability", "emptyProbability",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("emptyProbability"), Sp, FormulaDsl.Id("k"), Sp, FormulaDsl.Id("n"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Const("emptyWords"), Sp, FormulaDsl.Id("k"), Sp, FormulaDsl.Id("n"))), Sp, Dot, Sp, Const("card"), Sp, Colon, Sp, R())), Sp, Slash, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, R())), Sp, Seq(Caret, Grp(FormulaDsl.Id("n"))))),
                "The defining expression of emptyProbability.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("bpal-qseries", "QSeries",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("QSeries"), Sp, FormulaDsl.Id("k"), Sp, Eq, Sp, Const("PowerSeries"), Sp, Dot, Sp, Const("mk"), Sp, Parenthesized(Seq(Const("qCoeff"), Sp, FormulaDsl.Id("k"))))),
                "The defining expression of QSeries.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("bpal-eseries", "ESeries",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("ESeries"), Sp, FormulaDsl.Id("k"), Sp, Eq, Sp, Const("PowerSeries"), Sp, Dot, Sp, Const("mk"), Sp, Parenthesized(Seq(Const("fun"), Sp, Parenthesized(Seq(FormulaDsl.Id("m"), Sp, Colon, Sp, N())), Sp, Mapsto, Sp, Const("emptyProbability"), Sp, FormulaDsl.Id("k"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, FormulaDsl.Id("m"))))))),
                "The defining expression of ESeries.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("bpal-empty-centre-powerseries", "empty_centre_powerSeries",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, FormulaDsl.Id("k"))), Sp, Rightarrow, Sp, Parenthesized(Seq(Const("ESeries"), Sp, FormulaDsl.Id("k"), Sp, Eq, Sp, Parenthesized(Seq(D(1), Sp, Minus, Sp, Const("QSeries"), Sp, FormulaDsl.Id("k"))), Sp, Seq(Caret, Grp(Minus, D(1))))))),
                "The coefficient of degree m is the empty-centre probability at length 2m. Its convolution recursion gives the inverse of one minus the renewal series.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bpal-expectedwidth", "expectedWidth",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("n"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Const("expectedWidth"), Sp, FormulaDsl.Id("k"), Sp, FormulaDsl.Id("n"), Sp, Eq, Sp,
                    new Formula.Fraction(UniformWidthSum(), new Formula.Power(Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, R())), FormulaDsl.Id("n"))))),
                "The source states (arXiv v2, p. 5): “From the definition of expected value, it follows that Eₙ,ₖ = (1/kⁿ)∑ᵢ₌₁ⁿ i·LBPₖ(n,i).” The cardinality counts length-n words whose largest BP-factorization has width i; the empty word has width zero.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bpal-expectedwidth-limit", "expectedWidth_limit",
                Disp(Seq(Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, FormulaDsl.Id("k"))), Sp, Rightarrow, Sp, Parenthesized(Seq(Const("Tendsto"), Sp, Parenthesized(Seq(Const("expectedWidth"), Sp, FormulaDsl.Id("k"))), Sp, Const("atTop"), Sp, Parenthesized(Seq(Const("nhds"), Sp, Parenthesized(Seq(D(2), Sp, Slash, Sp, Parenthesized(Seq(D(1), Sp, Minus, Sp, FormulaDsl.Id("q"), Sp, FormulaDsl.Id("k"), Sp, Parenthesized(Seq(Const("uCount"), Sp, FormulaDsl.Id("k"))))), Sp, Minus, Sp, D(1))))))))),
                "The width equals twice the number of peeled pairs plus the indicator of a nonempty centre. Geometric domination of the tails and vanishing empty-centre probability give the stated limit.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bpal-claim", "claim",
                Disp(ClaimStatement()),
                "Conjecture 5 (arXiv v2, §3, p. 5): “Let k ≥ 2. Then E_k = 1+∑_{i=1}^∞ a_i k^{-i} where the sequence (a_n/2)_{n≥1} is A274199 in the On-Line Encyclopedia of Integer Sequences (OEIS).” A274199(d) is the stabilized diagonal a274190 (2*d) d. The positive index is i+1, so the source expansion starts with coefficients 2,4,6,10.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bpal-result", "result",
                Disp(Const("claim")),
                "For every alphabet size k≥2, every reverse-row coefficient converges, the positively indexed coefficient series is summable, and the expected largest width converges to one plus that series. The proof uses the exact renewal recursion and does not use the source Lemma 3.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gabric-shallit-2023-block-palindrome-expected-width"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula UniformWidthSum() => Seq(
        Sum, Underscore, Grp(Seq(FormulaDsl.Id("w"), Sp, Colon, Sp,
            Const("Fin"), Sp, FormulaDsl.Id("n"), Sp, To, Sp, Const("Fin"), Sp, FormulaDsl.Id("k"))), Sp,
        Parenthesized(Seq(Const("largestBPWidth"), Sp,
            Parenthesized(Seq(Const("List"), Dot, Const("ofFn"), Sp, FormulaDsl.Id("w"))), Sp, Colon, Sp, R())));
    private static Formula CoefficientTerm() => Seq(
        D(2), Sp, Cdot, Sp, FormulaDsl.Id("a"), Sp,
        Parenthesized(Seq(FormulaDsl.Id("i"), Sp, Plus, Sp, D(1))), Sp, Slash, Sp,
        new Formula.Power(Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, R())),
            Seq(FormulaDsl.Id("i"), Sp, Plus, Sp, D(1))));
    private static Formula CoefficientFunction() => Parenthesized(Seq(
        Const("fun"), Sp, Parenthesized(Seq(FormulaDsl.Id("i"), Sp, Colon, Sp, N())), Sp, Mapsto, Sp, CoefficientTerm()));
    private static Formula ClaimStatement() => Seq(
        Const("claim"), Sp, Iff, Sp, Forall, Sp, Parenthesized(Seq(FormulaDsl.Id("k"), Sp, Colon, Sp, N())), Sp, Comma, Sp,
        D(2), Sp, Leq, Sp, FormulaDsl.Id("k"), Sp, Rightarrow, Sp,
        Exists, Sp, Parenthesized(Seq(FormulaDsl.Id("a"), Sp, Colon, Sp, N(), Sp, To, Sp, R())), Sp, Comma, Sp,
        Parenthesized(Seq(Forall, Sp, FormulaDsl.Id("d"), Sp, Comma, Sp,
            Const("Tendsto"), Sp, Parenthesized(Seq(Const("fun"), Sp,
                Parenthesized(Seq(FormulaDsl.Id("N"), Sp, Colon, Sp, N())), Sp, Mapsto, Sp,
                Parenthesized(Seq(Const("a274190"), Sp, FormulaDsl.Id("N"), Sp,
                    Parenthesized(Seq(FormulaDsl.Id("N"), Sp, Minus, Sp, FormulaDsl.Id("d"))), Sp, Colon, Sp, R())))), Sp,
            Const("atTop"), Sp, Parenthesized(Seq(Const("nhds"), Sp,
                Parenthesized(Seq(FormulaDsl.Id("a"), Sp, FormulaDsl.Id("d"))))))), Sp, Land, Sp,
        Const("Summable"), Sp, CoefficientFunction(), Sp, Land, Sp,
        Const("Tendsto"), Sp, Parenthesized(Seq(Const("fun"), Sp, FormulaDsl.Id("n"), Sp, Mapsto, Sp,
            Const("expectedWidth"), Sp, FormulaDsl.Id("k"), Sp, FormulaDsl.Id("n"))), Sp, Const("atTop"), Sp,
        Parenthesized(Seq(Const("nhds"), Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp,
            Sum, Apos, Underscore, Grp(Seq(FormulaDsl.Id("i"), Sp, Colon, Sp, N())), Sp, CoefficientTerm())))));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Const(string name) => Seq(Operatorname, Grp(FormulaDsl.Id(name)));
    private static Formula N() => Seq(Mathbb, Grp(FormulaDsl.Id("N")));
    private static Formula R() => Seq(Mathbb, Grp(FormulaDsl.Id("R")));
}
