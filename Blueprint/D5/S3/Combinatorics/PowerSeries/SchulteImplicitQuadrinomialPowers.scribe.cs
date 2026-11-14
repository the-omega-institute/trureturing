using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class SchulteImplicitQuadrinomialPowersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/SchulteImplicitQuadrinomialPowers.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/schulte2015a262082");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native integer series and all its power coefficients.",
        H("Schulte's implicit quadrinomial power coefficients"), Blocks(
            Node("Native", "The native equation", NativeFormula(),
                "For a commutative coefficient ring R, Native(n,P) means exactly "
                + "P=1+X*P^n+X^2*P^(2*n)+X^3*P^(3*n) in R[[X]]. "
                + "All exponents and indices are natural numbers.", DescribeRole.Definition),
            Node("result", "Every coefficient of every positive power", ResultFormula(),
                "For every positive natural n there is exactly one integer formal power "
                + "series satisfying the native equation. For every such series P, every "
                + "positive natural m and every natural k, including zero, its degree-k "
                + "coefficient in P^m, mapped into the rationals, equals the displayed sum. "
                + "N abbreviates n*k+m and is positive. The sum includes j=0 and j=k. "
                + "Both subtractions in binomial indices are natural truncated subtraction; "
                + "binom(N,j)=0 for j>N. The prefactor and entire displayed sum are rational. "
                + "There is no upper restriction on k. Coefficient agreement gives integer "
                + "existence and uniqueness through the normalized contraction theorem. "
                + "Set Q(t)=1+t+t^2+t^3 and U(y)=y*P(y^n). The equation becomes "
                + "U=y*Q(U^n). Lagrange inversion at degree N and power m, followed by "
                + "the expansion coefficient map and the quadrinomial coefficient identity, "
                + "gives the formula. The polynomial identity's k<=3*N hypothesis follows "
                + "from n>=1 and m>=1. The statement concerns formal coefficients; the "
                + "source's separate lattice-path and logarithmic conjectures are outside it.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a262082-schulte-power-coefficient"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("schultea262082-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Open, V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body, Close);
    private static Formula NativeFormula()
    {
        var p = V("P"); var n = V("n"); var x = V("X");
        var rhs = Add(Add(Add(D(1), Mul(x, Pow(p, n))),
            Mul(Pow(x, D(2)), Pow(p, Mul(D(2), n)))),
            Mul(Pow(x, D(3)), Pow(p, Mul(D(3), n))));
        var body = All("n", N(), All("P", Series(V("R")),
            Seq(Call("Native", n, p), Sp, Iff, Sp, Eq(p, rhs))));
        return All("R", V("Type"), Seq(OpenBracket, Call("CommRing", V("R")),
            CloseBracket, Sp, body));
    }
    private static Formula ResultFormula()
    {
        var n = V("n"); var m = V("m"); var k = V("k"); var j = V("j"); var p = V("P");
        var degree = Add(Mul(n, k), m);
        var summand = Mul(Mul(Pow(Seq(Open, Minus, D(2), Close), j),
            Call("binom", degree, j)), Call("binom", Sub(Mul(D(3), degree), Mul(D(2), j)), Sub(k, j)));
        var sum = Seq(new Formula.Subscript(F.Sum, Eq(j, D(0))), Caret, Grp(k), Sp, summand);
        var identity = Eq(Call("ratCast", Call("coeff", k, Pow(p, m))),
            Mul(new Formula.Fraction(m, degree), sum));
        var unique = Call("ExistsUnique", Lam("P", Series(Z()), Call("Native", n, p)));
        var coefficients = All("P", Series(Z()), Imp(Call("Native", n, p),
            All("m", N(), Imp(Le(D(1), m), All("k", N(), identity)))));
        return All("n", N(), Imp(Le(D(1), n), And(unique, coefficients)));
    }
}
