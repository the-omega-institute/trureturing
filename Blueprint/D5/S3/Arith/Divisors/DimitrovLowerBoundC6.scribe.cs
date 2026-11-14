using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class DimitrovLowerBoundC6Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/DimitrovLowerBoundC6.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/dimitrov2026c6");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dimitrov's Conjecture 6 holds for every n ≥ 2 and k ≥ 1, with pointwise function-value powers.",
        H("Dimitrov's full Conjecture 6"),
        Blocks(
            Node("claim", "The complete original sixth conjecture", ClaimBody(),
                "The source is arXiv:2606.12484v1, Conjecture 6. Nat.totient is Euler's totient, "
                + "psi is Dedekind's function and ArithmeticFunction.sigma 1 is the positive-divisor sum. "
                + "All powers are powers of function values, all arithmetic in the inequality is real, "
                + "and the natural-number ranges n ≥ 2 and k ≥ 1 are unrestricted.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full sixth conjecture inequality", ClaimBody(),
                "Put a=φ(n)^k, b=ψ(n)^k and c=σ(n)^k, and write F for the three-term expression in the statement. "
                + "For A=a(b+c), B=b(a+c) and C=c(a+b), exact field normalization gives "
                + "(A+B+C)(1/A+1/B+1/C)=6+2F. The Conjecture 5 numerator is six times its denominator "
                + "plus the Conjecture 6 numerator, while the Conjecture 6 denominator is twice the Conjecture 5 denominator. "
                + "Applying DimitrovLowerBoundsC4C5.result5 and canceling this positive affine transformation proves the displayed bound. "
                + "The nonzero denominator facts follow from n ≥ 2 and positivity of the three arithmetic functions. "
                + "No new analytic inequality or additional hypothesis is needed. "
                + "The imported fifth-conjecture proof retains its existing Apache-2.0 supplier attribution and license.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("dimitrov-2606-12484-conjecture-6"), ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("dimitrov-c6-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula a = Pow(Cast(Call(Q("Nat", "totient"), n)), k);
        Formula b = Pow(Cast(Call(Named("psi"), n)), k);
        Formula c = Pow(Cast(Call(Q("ArithmeticFunction", "sigma"), D(1), n)), k);
        Formula lhs = Add(Add(Div(Mul(a, b), Mul(c, Add(a, b))),
            Div(Mul(a, c), Mul(b, Add(a, c)))), Div(Mul(b, c), Mul(a, Add(b, c))));
        Formula u = Pow(Sub(Cast(n), D(1)), Mul(D(2), k));
        Formula v = Pow(Sub(Pow(Cast(n), D(2)), D(1)), k);
        Formula w = Pow(Add(Cast(n), D(1)), Mul(D(2), k));
        Formula rhs = Div(Add(Add(Mul(D(4), u), v), w), Mul(D(2), Add(u, v)));
        return All("n", Naturals(), Imp(Le(D(2), n),
            All("k", Naturals(), Imp(Le(D(1), k), Ge(lhs, rhs)))));
    }

    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Reals()));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Ge(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
