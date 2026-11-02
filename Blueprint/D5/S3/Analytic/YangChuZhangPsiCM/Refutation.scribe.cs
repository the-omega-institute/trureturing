using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.YangChuZhangPsiCM;

internal sealed class RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/YangChuZhangPsiCM/Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/yangchuzhang2015psicm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive second derivative of G at x = 1/64 refutes the complete-monotonicity classification of -G.",
        H("Yang–Chu–Zhang Conjecture 1(ii)"), Blocks(
            Node("R", "Shifted digamma remainder", RFormula(),
                "Equation (1.10): R(x) = ψ(x + 1/2) − ln x. The argument x is real; the source uses x > 0. Equation (1.2), p. 1, defines ψ(x) = Γ′(x)/Γ(x) on positive real arguments. Here ψ is expressed through Complex.digamma and its real part; val(x, Complex) denotes the real-to-complex coercion.",
                DescribeRole.Definition, true),
            Node("G", "The source polynomial family", GFormula(),
                "Theorem 4, equation (3.3), defines Gₐ(x) = 24(x⁴ + ax² + (7/40)a − 31/336)R(x) − (x² − 7/40 + a). The real parameter a is unrestricted.",
                DescribeRole.Definition, true),
            Node("claim", "The source equivalence", Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                "Conjecture 1, p. 15: “Let R(x) be defined on (0, ∞) by (1.10). Then we conjecture that” “(ii) the function −Gₐ is completely monotone on (0, ∞) if and only if a ≤ 155/294.” The existing CompletelyMonotoneOn predicate means ContDiffOn Real ⊤ on Set.Ioi 0 together with nonnegative signed iterated derivatives for every natural order, including zero, at every positive real point. All real a are quantified, and both directions of the equivalence are retained.",
                DescribeRole.Definition, true),
            Node("result", "Failure of the sufficient direction", new Formula.Not(Parenthesized(ClaimBody())),
                "At a = 155/294 − 1/10000 = 774853/1470000 and x = 1/64, the second derivative of G is greater than 1/2. Thus the second derivative of −G is negative although a < 155/294. The estimate uses the digamma derivative series, a reciprocal-cube tail bounded by a telescoping sum, and exact rational inequalities. The bound on the second derivative holds for every a ≥ 774853/1470000.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, bool literature) =>
        Describe.Lean(DescribeId.Create("ycz-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("ycz2015-psicm"), ResolutionKind.Refuted) : null);

    private static Formula RFormula()
    {
        Formula x = F.Id("x");
        return All("x", F.Id("Real"), Equal(Call("R", x),
            Subtract(App(Qualified("Complex", "re"), App(Qualified("Complex", "digamma"),
                Call("val", Add(x, FracOf(1, 2)), F.Id("Complex")))),
                App(Qualified("Real", "log"), x))));
    }

    private static Formula GFormula()
    {
        Formula a = F.Id("a");
        Formula x = F.Id("x");
        Formula polynomial = Subtract(Add(Add(Pow(x, 4), Multiply(a, Pow(x, 2))),
            Multiply(FracOf(7, 40), a)), FracOf(31, 336));
        Formula correction = Add(Subtract(Pow(x, 2), FracOf(7, 40)), a);
        return All("a", F.Id("Real"), All("x", F.Id("Real"), Equal(Call("G", a, x),
            Subtract(Multiply(Multiply(Num(24), Parenthesized(polynomial)), Call("R", x)),
                Parenthesized(correction)))));
    }

    private static Formula ClaimBody()
    {
        Formula a = F.Id("a");
        Formula x = F.Id("x");
        Formula function = Seq(Operatorname, Grp(F.Id("fun")), Sp,
            Parenthesized(Seq(x, Colon, Sp, F.Id("Real"))), Sp, Mapsto, Sp,
            new Formula.Negate(Call("G", a, x)));
        Formula cm = App(Qualified("D5", "S3", "Analytic", "ExpRatioCM", "Defs", "CompletelyMonotoneOn"),
            Parenthesized(function));
        return All("a", F.Id("Real"), new Formula.Logic(cm, FormulaLogicOperator.Iff,
            new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, FracOf(155, 294))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(F.Id(name), arguments);
    private static Formula FracOf(long numerator, long denominator) =>
        new Formula.Fraction(Num(numerator), Num(denominator));
    private static Formula Pow(Formula value, long exponent) => new Formula.Power(value, Num(exponent));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(params string[] names) =>
        Seq(names.SelectMany((name, index) => index == 0
            ? new[] { Operatorname, Grp(F.Id(name)) }
            : new[] { Dot, Operatorname, Grp(F.Id(name)) }).ToArray());
}
