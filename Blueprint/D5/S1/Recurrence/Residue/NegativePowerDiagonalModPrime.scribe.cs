using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class NegativePowerDiagonalModPrimeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.";
    private static readonly LibraryNoteRef SourceTwo =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2016a266489");
    private static readonly LibraryNoteRef SourceThree =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2026a395833");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One general theorem proves a congruence clause for each of two negative-power diagonal sequences.",
        H("Negative-Power Diagonals Modulo a Prime"),
        Blocks(
            Paragraph(Text("The notes hanna2016a266489 and hanna2026a395833 record Hanna's "
                + "two generating equations and their respective mod-two and mod-three "
                + "conjectures. One general theorem implies one clause of each entry. "
                + "These are two different sequences; no equivalence is asserted.")),
            Paragraph(Text("All parameters, degrees, approximation depths, and exponents "
                + "are natural numbers; subtraction in these expressions is natural subtraction. "
                + "The coefficients a(p,n) are integers. Write A(p) for generatingSeries(p) "
                + "and P(p,d) for its integer-series approximation at depth d. The comparison "
                + "series B is also over the integers. The symbols 1 and X in a series "
                + "expression denote the constant series one and the formal variable.")),
            Paragraph(Text("The operator coeff(n,f) extracts a coefficient, mk forms a series "
                + "from a coefficient function, and subst(f,g) means f composed with g. "
                + "The expression invOfUnit(f,1) is the formal unit inverse when coeff(0,f)=1, "
                + "as proved for A(p) and assumed for B. Thus the substitution is exactly "
                + "A(x/A(x)^e), with e=(p-1)(n-1)+1. Integer divisibility is used below; "
                + "intCast(p) explicitly casts the natural parameter to an integer.")),
            Node("a", "The triangular coefficient construction", CoefficientDefinition(),
                "Starting with P(p,0)=1, the update sets the first two coefficients to one "
                + "and solves every higher diagonal equation for its leading coefficient. "
                + "The summand at j=0 is zero in positive degree. Every positive j below n "
                + "uses only coefficients below n, including those of the inverse power. "
                + "Agreement below a degree therefore extends by one degree after each update.",
                DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series",
                Disp(Seq(Bound("p", Naturals()),
                    Equal(A(), Call("mk", Lambda("n", Call("a", P(), N())))))),
                "The stabilized coefficients form A(p) over the integers.", DescribeRole.Definition),
            Node("generating_equation", "The normalized substitution equation",
                Disp(Seq(Bound("p", Naturals()),
                    Conjunction(Equal(Coefficient(D(0), A()), D(1)),
                        Conjunction(Equal(Coefficient(D(1), A()), D(1)), Equation(A()))))),
                "The coefficient of the substitution is a finite sum through outer degree n. "
                + "Its degree-n summand is a(p,n), since the inverse power has constant "
                + "coefficient one. The remaining sum is exactly the triangular update. "
                + "Stabilization gives a fixed point, hence the stated equation for every n>1."),
            Node("generating_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "The equation is equivalent to being a fixed point of the triangular update. "
                + "The inverse-difference identity preserves agreement below each degree, "
                + "and the update improves that agreement by one. Induction on the degree "
                + "therefore identifies B with A(p)."),
            Node("diagonal_conjecture_general", "The prime-parameter congruence",
                Disp(Seq(Bound("p", Naturals()),
                    Implication(Call("Prime", P()), Seq(Bound("n", Naturals()),
                        Implication(AtLeastTwo(),
                            Divides(Call("intCast", P()), Call("a", P(), N()))))))),
                "For n=r+1>1 the residual of 1+X is (-1)^r choose(p*r,r), obtained by "
                + "rescaling the geometric series. Mathlib's choose_mul_right gives the "
                + "exact identity choose(p*r,r)=p*choose(p*r-1,r-1), so this residual "
                + "vanishes modulo p. The update commutes with reduction of integer "
                + "coefficients. Its uniqueness over ZMod(p) identifies the reduction "
                + "of A(p) with 1+X, whose coefficients above degree one vanish."),
            Node("hanna_conjecture_a266489", "A266489: congruence clause (C2)",
                InstanceFormula(D(2)),
                "At p=2 the exponent (p-1)(n-1)+1 equals n for n>1. The normalized "
                + "generating equation is therefore that of hanna2016a266489. The general "
                + "theorem at the prime two proves exactly its clause (C2).",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SourceTwo),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a266489-negative-power-diagonal-mod-two"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_a395833", "A395833: the mod-three clause",
                InstanceFormula(D(3)),
                "At p=3 the exponent (p-1)(n-1)+1 equals 2*n-1 for n>1. The normalized "
                + "generating equation is therefore that of hanna2026a395833. The general "
                + "theorem at the prime three proves its quoted mod-three clause.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SourceThree),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a395833-negative-power-diagonal-mod-three"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("negative-diagonal-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula P() => F.Id("p");
    private static Formula N() => F.Id("n");
    private static Formula A() => Call("A", P());
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Coefficient(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula Exponent() =>
        Add(Mul(Subtract(P(), D(1)), Subtract(N(), D(1))), D(1));
    private static Formula Equation(Formula f) => Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, N()), Equal(Coefficient(N(),
            Call("subst", f, Mul(F.Id("X"), Power(Call("invOfUnit", f, D(1)), Exponent())))), D(0))));
    private static Formula AtLeastTwo() => Seq(D(2), Sp, Le, Sp, N());
    private static Formula InstanceFormula(Formula prime) => Disp(Seq(Bound("n", Naturals()),
        Implication(AtLeastTwo(), Divides(prime, Call("a", prime, N())))));

    private static Formula CoefficientDefinition()
    {
        var d = F.Id("d");
        var j = F.Id("j");
        var approximation = Call("P", P(), d);
        var summand = Mul(Coefficient(j, approximation),
            Coefficient(Subtract(N(), j),
                Power(Call("invOfUnit", approximation, D(1)), Mul(Exponent(), j))));
        var sum = Seq(new Formula.Subscript(F.Sum,
            Seq(j, Sp, InMacro, Sp, Call("range", N()))), Sp, Parenthesized(summand));
        var next = Seq(Named("if"), Sp, Parenthesized(Seq(N(), Sp, Le, Sp, D(1))),
            Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, Minus, Parenthesized(sum));
        return Disp(new Formula.Aligned([
            Seq(Bound("p", Naturals()), Equal(Call("P", P(), D(0)), D(1))),
            Seq(Bound("p", Naturals()), Bound("d", Naturals()),
                Equal(Call("P", P(), Add(d, D(1))), Call("mk", Lambda("n", next)))),
            Seq(Bound("p", Naturals()), Bound("n", Naturals()),
                Equal(Call("a", P(), N()), Coefficient(N(), Call("P", P(), Add(N(), D(1))))))
        ]));
    }

    private static Formula UniqueFormula()
    {
        var b = F.Id("B");
        return Disp(Seq(Bound("p", Naturals()), Bound("B", Call("PowerSeries", Integers())),
            Implication(Equal(Coefficient(D(0), b), D(1)),
                Implication(Equal(Coefficient(D(1), b), D(1)),
                    Implication(Equation(b), Equal(b, A()))))));
    }
}
