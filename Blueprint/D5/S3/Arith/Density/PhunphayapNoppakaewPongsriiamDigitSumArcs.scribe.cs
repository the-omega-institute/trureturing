using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Density;

internal sealed class PhunphayapNoppakaewPongsriiamDigitSumArcsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Density/PhunphayapNoppakaewPongsriiamDigitSumArcs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/phunphayap2023digitsumarcs");

    private const string Question =
        "Question 3 (arXiv:2303.13017v1, p. 10): “We obtain in Theorem 2 that Out(s_b, n) "
        + "contains every multiple of s_b(n). Does Out(s_b, n) contain an infinite number of "
        + "positive integers that are not divisible by s_b(n)? When d = 1 and s_b(n) ≥ 2, "
        + "the answer is yes. Can we determine a simple necessary and sufficient condition "
        + "for the infinitely many elements in A ∩ Out(s_b, n) where A is the set of positive "
        + "integers that are not divisible by s_b(n)? In that case, does Out(s_b, n) has a natural density?”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The attainable positive digit sums of multiples form an additive semigroup whose gcd "
        + "determines its eventual support and density.",
        H("Digit-Sum Arcs: Infinitude and Natural Density"),
        Blocks(
            Paragraph(Text("All number variables are natural numbers, with positivity stated "
                + "explicitly. Nat.digits lists the digits from least to most significant. "
                + "The digit sum is List.sum (Nat.digits b N). Set.ncard counts the finite "
                + "intersection with the inclusive interval [1,x]; ratios and density values are real.")),
            Node("out", "Positive outgoing digit-sum arcs", "Out", OutFormula(),
                "The source defines an arc on p. 2: “We say that there exists a g-directed edge "
                + "or g-arc from n to u if there exists a positive integer N such that N is "
                + "divisible by n and g(N) = u.” It then sets “Out(g, n) = {u ∈ ℕ | n →g u}.” "
                + "Here g is the base-b digit sum, and both u and N are positive. On p. 3 the "
                + "examples are s₁₀(123) = 6 and s₅(123) = 11.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The answer to Question 3", "claim",
                Disp(Iff(F.Id("claim"), ClaimBody())),
                Question + " The answer holds for every base b ≥ 2 and positive n. Writing "
                + "d = Nat.gcd (b − 1) n, the intersection in the question is infinite exactly "
                + "when d is smaller than List.sum (Nat.digits b n), and the density is 1/d.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Infinitude Criterion and Density"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Concatenation of digit blocks closes Out under addition. "
                    + "If n < b^L, the multiple n(b^L−1) has digit sum (b−1)L. Two adjacent "
                    + "lengths show that the gcd of Out is Nat.gcd (b−1) n. The numerical "
                    + "semigroup theorem then puts every sufficiently large positive multiple "
                    + "of this gcd in Out. If the digit sum of n exceeds the gcd, an arithmetic "
                    + "progression gives infinitely many such elements not divisible by that "
                    + "digit sum; if they are equal, none exists. The count of multiples differs "
                    + "from the count of Out in [1,x] by a bounded amount, giving density 1/d."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("phunphayap-noppakaew-pongsriiam-2023-digit-sum-arcs"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))),
        DescribeRole.Definition);

    private static Formula OutFormula()
    {
        var b = F.Id("b"); var n = F.Id("n"); var u = F.Id("u"); var bigN = F.Id("N");
        return Disp(All("b", Naturals(), All("n", Naturals(), Equal(Call("Out", b, n),
            SetOf("u", And(Less(D(0), u), Exists("N", Naturals(),
                And(Less(D(0), bigN), And(Divides(n, bigN), Equal(DigitSum(b, bigN), u))))))))));
    }

    private static Formula DensityBody(Formula s, Formula delta)
    {
        var x = F.Id("x");
        var interval = App(Q("Set", "Icc"), D(1), x);
        var count = App(Q("Set", "ncard"), App(Q("Set", "inter"), s, interval));
        var ratio = new Formula.Fraction(Cast(count, Reals()), Cast(x, Reals()));
        var sequence = Seq(Operatorname, Grp(F.Id("fun")), Sp, Parenthesized(Seq(x, Colon, Sp, Naturals())), Sp,
            Mapsto, Sp, ratio);
        return App(Q("Filter", "Tendsto"), Parenthesized(sequence),
            Q("Filter", "atTop"), Call("nhds", delta));
    }

    private static Formula ClaimBody()
    {
        var b = F.Id("b"); var n = F.Id("n");
        var d = App(Q("Nat", "gcd"), Parenthesized(Subtract(b, D(1))), n);
        var sum = DigitSum(b, n);
        var excluded = SetOf("u", Divides(sum, F.Id("u")));
        var difference = Parenthesized(Seq(Call("Out", b, n), Sp, Setminus, Sp, excluded));
        var infinite = App(Q("Set", "Infinite"), difference);
        return All("b", Naturals(), All("n", Naturals(),
            Implies(Le(D(2), b), Implies(Le(D(1), n),
                And(Iff(infinite, Less(d, sum)), DensityBody(Call("Out", b, n),
                    new Formula.Fraction(D(1), Cast(d, Reals()))))))));
    }

    private static Formula DigitSum(Formula b, Formula n) =>
        App(Q("List", "sum"), App(Q("Nat", "digits"), b, n));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula SetOf(string variable, Formula body) =>
        Seq(OpenBrace, F.Id(variable), Sp, Colon, Sp, Naturals(), Sp, Mid, Sp, body, CloseBrace);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
