using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Density;

internal sealed class ChuMillerTreschGammaSplitGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/chumillertresch2025diophantine");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every prescribed Gamma-label density has a positive increasing linear-growth sequence.",
        H("Linear Growth for Every Gamma-Label Split"),
        Blocks(
            Paragraph(Text("All sequence indices and Diophantine variables are natural numbers, "
                + "including zero. Nat.div is natural integer division, subtraction in the naturals "
                + "truncates at zero, and the displayed density ratio uses real division. "
                + "Sequences start at index zero; prefix counts start at edge one.")),
            Node("gamma", "The gcd-reduced Diophantine label", "Gamma", GammaFormula(),
                "Section 1, pp. 2–3: “Γ : ℕ² → {0, 1} … where Γ(a, b) = 0 if "
                + "(a/gcd(a, b)) x + (b/gcd(a, b)) y = (a/gcd(a, b) − 1)(b/gcd(a, b) − 1)/2 "
                + "has the nonnegative integral solution, and Γ(a, b) = 1 if 1 + (a/gcd(a, b)) x "
                + "+ (b/gcd(a, b)) y = (a/gcd(a, b) − 1)(b/gcd(a, b) − 1)/2 has the nonnegative "
                + "integral solution.” The function Gamma returns 0 when the first equation has "
                + "a solution in ℕ and 1 otherwise. Theorem 1.1 identifies this latter case with "
                + "the second equation for positive inputs.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("zero-count", "The inclusive prefix count", "zeroCount", ZeroCountFormula(),
                "Corollary 2.6, p. 5, counts “#{n ≤ N : Γ(a_{n−1}, a_n) = 0}”. "
                + "The count zeroCount uses 1 ≤ n ≤ N, so that the first pair is (a 0, a 1) "
                + "and the prefix contains exactly N edges.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Polynomial growth for a prescribed split", "claim",
                Disp(Iff(F.Id("claim"), ClaimBody())),
                "Section 3.4, p. 11: “As noted in Remark 2.7, the sequence grows exponentially "
                + "fast (faster than the Fibonacci sequence). Is there a construction involving "
                + "a strictly increasing sequence that grows slower than the Fibonacci sequence, "
                + "or perhaps even like n^k for some k?” The real parameter p ranges over [0,1]. "
                + "The sequence has positive natural entries, a polynomial upper bound from "
                + "index one, and limiting proportion p of zero-labelled edges.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "An affirmative answer with exponent one", "result", Disp(ClaimBody()),
                "The chains (3,7,17,19,23,43) and (3,23,27,29,33,43), translated by 40k, "
                + "have respectively five zero-labelled and five one-labelled edges. Their endpoints "
                + "agree across consecutive translates. The floor increment ⌊(k+1)p⌋−⌊kp⌋ "
                + "selects a chain for each k. The resulting sequence satisfies 8n ≤ a n + 9 "
                + "and a n ≤ 8n + 15, while 0 ≤ pN − zeroCount a N < 5. Squeezing the real "
                + "ratios gives the required limit, including p=0 and p=1. The polynomial bound "
                + "uses k=1 and C=23. No assertion of optimality of the coefficient is made.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chu-miller-tresch-2025-gamma-split-linear-growth"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula GammaFormula()
    {
        var a = F.Id("a"); var b = F.Id("b");
        var gcd = App(Q("Nat", "gcd"), a, b);
        var left = App(Q("Nat", "div"), a, gcd);
        var right = App(Q("Nat", "div"), b, gcd);
        var equation = Equal(Add(Multiply(left, F.Id("x")), Multiply(right, F.Id("y"))),
            App(Q("Nat", "div"), Parenthesized(Multiply(
                Parenthesized(Subtract(left, D(1))), Parenthesized(Subtract(right, D(1))))), D(2)));
        var soluble = ExistsOne("x", Naturals(), ExistsOne("y", Naturals(), equation));
        var value = Parenthesized(Seq(Named("if"), Sp, Parenthesized(soluble), Sp,
            Named("then"), Sp, D(0), Sp, Named("else"), Sp, D(1)));
        return Disp(All("a", Naturals(), All("b", Naturals(),
            Equal(Call("Gamma", a, b), value))));
    }

    private static Formula ZeroCountFormula()
    {
        var a = F.Id("a"); var n = F.Id("n"); var bigN = F.Id("N");
        var edge = Equal(Call("Gamma", App(a, Parenthesized(Subtract(n, D(1)))), App(a, n)), D(0));
        var filtered = App(Q("Finset", "filter"), Parenthesized(LambdaTerm("n", Naturals(), edge)),
            Parenthesized(App(Q("Finset", "Icc"), D(1), bigN)));
        return Disp(All("a", FunctionType(Naturals(), Naturals()), All("N", Naturals(),
            Equal(Call("zeroCount", a, bigN), App(Q("Finset", "card"), Parenthesized(filtered))))));
    }

    private static Formula ClaimBody()
    {
        var p = F.Id("p"); var a = F.Id("a"); var n = F.Id("n"); var bigN = F.Id("N");
        var growth = ExistsOne("k", Naturals(), ExistsOne("C", Reals(),
            All("n", Naturals(), Implies(AtMost(D(1), n),
                AtMost(Cast(App(a, n), Reals()), Multiply(F.Id("C"),
                    new Formula.Power(Cast(n, Reals()), F.Id("k"))))))));
        var ratio = new Formula.Fraction(Cast(Call("zeroCount", a, bigN), Reals()), Cast(bigN, Reals()));
        var density = App(Q("Filter", "Tendsto"), Parenthesized(LambdaTerm("N", Naturals(), ratio)),
            Q("Filter", "atTop"), Call("nhds", p));
        var body = And(Call("StrictMono", a), And(All("n", Naturals(), Less(D(0), App(a, n))),
            And(growth, density)));
        return All("p", Reals(), Implies(AtMost(D(0), p), Implies(AtMost(p, D(1)),
            ExistsOne("a", FunctionType(Naturals(), Naturals()), body))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula FunctionType(Formula source, Formula target) => Seq(source, Sp, To, Sp, target);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula LambdaTerm(string name, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
