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
        Describe.Lean(DescribeId.Create("capitelli-somma-" + name.ToLowerInvariant()),
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
