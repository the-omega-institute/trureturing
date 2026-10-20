using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class CapitelliSommaAllOddNonconvergenceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/capitellisomma2024subtraction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-odd finite subtraction games have nonconvergent winning probabilities.",
        H("Nonconvergence for all-odd subtraction games"),
        Blocks(
            Node("legalMoves", "Legal subtractions", LegalMovesBody(),
                "Section 1, p. 2: “At a given position (number of chips in the pile) 0 ≤ m ≤ n, "
                + "an element k′ ∈ {k ∈ S | k ≤ m} is randomly selected with equal probability, "
                + "and the next player to move removes k′ chips from the pile.” "
                + "The paper takes S to consist of positive integers. Here S is a finite set of natural numbers; "
                + "the filter explicitly requires a positive subtraction and includes precisely those at most n.",
                AssessedProvenance.FromLiterature(Source)),
            Node("winProb", "Probability of winning", WinProbBody(),
                "Section 1, p. 2: “The first player who is confronted with a position m for which "
                + "{k ∈ S | k ≤ m} = ∅, loses.” The function winProb S n is the probability that the next player wins. "
                + "It is zero without a legal move and otherwise one minus the uniform average of the follower probabilities. "
                + "The sum uses attach, whose elements carry their membership proofs; val is the underlying natural number. "
                + "Subtraction of natural indices is truncated subtraction. The cardinality is cast to the reals, "
                + "and the displayed quotient is real division. Recursion terminates because each legal subtraction is positive.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The all-odd conjecture", Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                "Section 3, p. 7: “However, we do not show that an all-odd subtraction set necesarily do not "
                + "converge (although we conjeture it) nor we provide the exact limits of the even and odd "
                + "subsequences for the (conjectured) non-convergent case.” "
                + "The section assumes a finite nonempty subtraction set with gcd one. "
                + "Odd natural numbers are positive, and nonconvergence means that no real limit exists.",
                AssessedProvenance.FromLiterature(Source)),
            Node("b", "Alternating probability transform", BBody(),
                "The private definition b uses real powers and real arithmetic.",
                AssessedProvenance.FromRepo(Source)),
            Node("d", "Adjacent transformed probabilities", DBody(),
                "The private definition d adds consecutive values of b.",
                AssessedProvenance.FromRepo(Source)),
            Node("d_threshold", "A newly legal subtraction", ThresholdBody(),
                "The private d_threshold identity includes the changing-denominator term b S n + 1. "
                + "The cardinality is cast to the reals before adding one.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Lemma),
            Node("d_initial", "Before the first legal subtraction", InitialBody(),
                "The private d_initial identity covers both possibilities for the next pile size.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Lemma),
            Node("d_nonneg", "Nonnegative adjacent sums", NonnegBody(),
                "The private d_nonneg theorem uses strong induction through changes of legal moves; "
                + "it requires neither nonemptiness nor a gcd hypothesis.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Lemma),
            Node("d_seed", "The positive seed at the least subtraction", SeedBody(),
                "The private d_seed theorem assumes membership and minimality of m. "
                + "Natural subtraction in m - 1 is truncated.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Lemma),
            Node("invariant", "The finite adjacent-sum window", InvariantBody(),
                "The private invariant definition sums over Finset.range s. "
                + "The index N - s + r means truncated natural subtraction followed by addition.",
                AssessedProvenance.FromRepo(Source)),
            Node("invariant_step", "Conservation after all moves are legal", InvariantStepBody(),
                "The private invariant_step theorem applies when N bounds every element of S.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Lemma),
            Node("invariant_constant", "The conserved window at every later index", InvariantConstantBody(),
                "The private invariant_constant theorem iterates conservation from any upper bound M.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Lemma),
            Node("invariant_positive", "The conserved window is at least two", InvariantPositiveBody(),
                "The private invariant_positive theorem evaluates the window at Finset.max' S hne. "
                + "Here hne is the proof of nonemptiness required by Finset.max'.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Lemma),
            Node("nonconvergence", "Nonconvergence without a gcd hypothesis", NonconvergenceBody(),
                "The private nonconvergence theorem is the stronger statement consumed by result. "
                + "Its hypotheses are exactly nonemptiness and oddness of every subtraction.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("result", "Every all-odd subtraction set fails to converge", ClaimBody(),
                "Put b(n)=(-1)^n(1-2 winProb S n) and d(n)=b(n)+b(n+1). "
                + "Oddness makes b satisfy a positive averaging recurrence. At a newly legal subtraction, "
                + "the change in the averaging denominator contributes b(n)+1, which is nonnegative since b(n) lies between minus one and one. "
                + "Strong induction gives d(n) nonnegative, with d(m-1)=2 at the first legal move m=min S. "
                + "For N at least max S, the finite sum over s in S and r<s of d(N-s+r) is conserved by telescoping "
                + "and is at least two. Convergence of winProb would force d, and hence this finite sum, to tend to zero. "
                + "This contradiction proves the proposition. The argument also applies without the gcd hypothesis. "
                + "It does not determine the even and odd subsequence limits or the multiplicities of the characteristic roots.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("capitelli-somma-2024-all-odd-nonconvergence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("capitelli-somma-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula SetType => Call("Finset", Nat);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(name), Colon, type)), Mapsto, body));
    private static Formula Legal(Formula s, Formula n) => Call("legalMoves", s, n);
    private static Formula Prob(Formula s, Formula n) => Call("winProb", s, n);
    private static Formula Nonempty(Formula s) => App(Qualified("Finset", "Nonempty"), s);
    private static Formula Odds(Formula s) =>
        All("s", Nat, Imp(Member(F.Id("s"), s), Call("Odd", F.Id("s"))));
    private static Formula Bound(Formula s, Formula n) =>
        All("s", Nat, Imp(Member(F.Id("s"), s), Leq(F.Id("s"), n)));
    private static Formula SumOver(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(F.Id(name), set)), Sp, Parenthesized(body));

    private static Formula BBody()
    {
        var s = F.Id("S"); var n = F.Id("n");
        var sign = new Formula.Power(Parenthesized(Seq(Minus, D(1), Colon, Real)), n);
        return All("S", SetType, All("n", Nat, Equal(Call("b", s, n),
            Multiply(sign, Parenthesized(Subtract(D(1), Multiply(D(2), Prob(s, n))))))));
    }

    private static Formula DBody()
    {
        var s = F.Id("S"); var n = F.Id("n");
        return All("S", SetType, All("n", Nat, Equal(Call("d", s, n),
            Add(Call("b", s, n), Call("b", s, Add(n, D(1)))))));
    }

    private static Formula ThresholdBody()
    {
        var s = F.Id("S"); var n = F.Id("n"); var k = F.Id("s");
        var legal = Legal(s, n);
        var card = Parenthesized(Seq(App(Qualified("Finset", "card"), legal), Colon, Real));
        var sum = SumOver("s", legal, Call("d", s, Parenthesized(Subtract(n, k))));
        return All("S", SetType, Imp(Odds(s), All("n", Nat,
            Imp(Nonempty(legal), Imp(Member(Add(n, D(1)), s),
                Equal(Multiply(Parenthesized(Add(card, D(1))), Call("d", s, n)),
                    Add(Add(sum, Call("b", s, n)), D(1))))))));
    }

    private static Formula InitialBody()
    {
        var s = F.Id("S"); var n = F.Id("n");
        var value = Seq(Named("if"), Sp, Member(Add(n, D(1)), s), Sp,
            Named("then"), Sp, D(2), Sp, Named("else"), Sp, D(0));
        return All("S", SetType, Imp(Odds(s), All("n", Nat,
            Imp(Equal(Legal(s, n), Emptyset), Equal(Call("d", s, n), value)))));
    }

    private static Formula NonnegBody()
    {
        var s = F.Id("S"); var n = F.Id("n");
        return All("S", SetType, Imp(Odds(s), All("n", Nat, Leq(D(0), Call("d", s, n)))));
    }

    private static Formula SeedBody()
    {
        var s = F.Id("S"); var m = F.Id("m"); var k = F.Id("s");
        var minimum = All("s", Nat, Imp(Member(k, s), Leq(m, k)));
        return All("S", SetType, Imp(Odds(s), All("m", Nat, Imp(Member(m, s),
            Imp(minimum, Equal(Call("d", s, Parenthesized(Subtract(m, D(1)))), D(2)))))));
    }

    private static Formula InvariantBody()
    {
        var s = F.Id("S"); var n = F.Id("N"); var k = F.Id("s"); var r = F.Id("r");
        var index = Parenthesized(Add(Parenthesized(Subtract(n, k)), r));
        return All("S", SetType, All("N", Nat, Equal(Call("invariant", s, n),
            SumOver("s", s, SumOver("r", App(Qualified("Finset", "range"), k), Call("d", s, index))))));
    }

    private static Formula InvariantStepBody()
    {
        var s = F.Id("S"); var n = F.Id("N");
        return All("S", SetType, Imp(Odds(s), Imp(Nonempty(s), All("N", Nat,
            Imp(Bound(s, n), Equal(Call("invariant", s, Add(n, D(1))), Call("invariant", s, n)))))));
    }

    private static Formula InvariantConstantBody()
    {
        var s = F.Id("S"); var m = F.Id("M"); var n = F.Id("n");
        return All("S", SetType, Imp(Odds(s), Imp(Nonempty(s), All("M", Nat,
            Imp(Bound(s, m), All("n", Nat,
                Equal(Call("invariant", s, Add(m, n)), Call("invariant", s, m))))))));
    }

    private static Formula InvariantPositiveBody()
    {
        var s = F.Id("S"); var hne = F.Id("hne");
        var maximum = App(Seq(Named("Finset"), Dot, Operatorname, Grp(F.Id("max"), Apos)), s, hne);
        var positive = Seq(Forall, Sp, Parenthesized(Seq(hne, Colon, Nonempty(s))), Comma, Sp,
            Leq(D(2), Call("invariant", s, maximum)));
        return All("S", SetType, Imp(Odds(s), positive));
    }

    private static Formula NonconvergenceBody()
    {
        var s = F.Id("S"); var l = F.Id("L");
        var limit = App(Qualified("Filter", "Tendsto"), App(Named("winProb"), s),
            Qualified("Filter", "atTop"), Call("nhds", l));
        return All("S", SetType, Imp(Nonempty(s), Imp(Odds(s),
            Seq(Neg, Parenthesized(Some("L", Real, limit))))));
    }

    private static Formula LegalMovesBody()
    {
        var s = F.Id("S"); var n = F.Id("n"); var k = F.Id("s");
        return All("S", SetType, All("n", Nat, Equal(Legal(s, n),
            App(Qualified("Finset", "filter"), Fn("s", Nat, And(Less(D(0), k), Leq(k, n))), s))));
    }

    private static Formula WinProbBody()
    {
        var s = F.Id("S"); var n = F.Id("n"); var k = F.Id("s");
        var legal = Legal(s, n);
        var nonempty = App(Qualified("Finset", "Nonempty"), legal);
        var indices = App(Qualified("Finset", "attach"), legal);
        var sum = Seq(new Formula.Subscript(Sum, Member(k, indices)), Sp,
            Prob(s, Parenthesized(Seq(n, Minus, Call("val", k)))));
        var denominator = Parenthesized(Seq(App(Qualified("Finset", "card"), legal), Colon, Real));
        var value = Seq(Named("if"), Sp, nonempty, Sp, Named("then"), Sp,
            D(1), Minus, new Formula.Fraction(sum, denominator), Sp, Named("else"), Sp, D(0));
        return All("S", SetType, All("n", Nat, Equal(Prob(s, n), value)));
    }

    private static Formula ClaimBody()
    {
        var s = F.Id("S"); var k = F.Id("s"); var l = F.Id("L"); var n = F.Id("n");
        var odds = All("s", Nat, Imp(Member(k, s), Call("Odd", k)));
        var gcd = Equal(App(Qualified("Finset", "gcd"), s, Named("id")), D(1));
        var limit = App(Qualified("Filter", "Tendsto"), Fn("n", Nat, Prob(s, n)),
            Qualified("Filter", "atTop"), Call("nhds", l));
        return All("S", SetType, Imp(App(Qualified("Finset", "Nonempty"), s),
            Imp(odds, Imp(gcd, Seq(Neg, Parenthesized(Some("L", Real, limit)))))));
    }
}
