using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaPrimeSubstitutionIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaPrimeSubstitutionIntegrality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2016a271931");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every prime exponent has a normalized integer power series satisfying Hanna's substitution equation.", H("Integral solutions for prime substitution exponents"), Blocks(
            Paragraph(Text("PowerSeries.subst takes the inner series first. Coefficients and indices use the displayed rings and natural numbers. A zero constant coefficient and linear coefficient one express G(0)=0 and G'(0)=1. Raising the equation to the pth power expresses the source root with leading coefficient one. Modulo p, Frobenius makes every residual coefficient divisible by p; successive coefficient corrections stabilize to an integer series.")),
            Node("claim", "Hanna's prime-exponent conjecture", Disp(Iffn(Named("claim"), ClaimBody())),
                "OEIS A271931, A271932 and A271933, COMMENTS (unpaginated): \"More generally, for prime p there exists an integer series G(x) that satisfies: G(x) = G( x^p + p*x*G(x)^p )^(1/p) with G(0)=0, G'(0)=1 (conjecture).\" Integer series means PowerSeries over the integers; the chosen root has linear coefficient one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("General.inner", "The substitution argument", InnerFormula(),
                "The argument is X to the power p plus c times X times the pth power of f.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("General.inner_zero", "The substitution argument has zero constant coefficient",
                Disp(Ring(All("p", N(), Imp(Rel(D(0), Lt, V("p")), All("c", V("R"),
                    All("f", Series(V("R")), Eqn(Call("constantCoeff", App(Qualified("General", "inner"), V("p"), V("c"), V("f"))), D(0)))))))),
                "For a positive exponent the substitution argument has zero constant coefficient, so formal substitution is defined.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("General.Lifting.exists_lifted", "Triangular coefficient lifting", LiftingFormula(),
                "Suppose equal initial coefficients make residuals agree to a shifted order, their first possible difference is a times the new coefficient difference, and q cancels each residual coefficient after multiplication by a. A base residual vanishing through the initial shifted order then lifts to a series with residual zero. At each stage one coefficient is corrected; stabilization defines the limiting coefficient function.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("General.solution_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "Over a commutative ring without zero divisors, a nonzero exponent coefficient forces two normalized solutions to coincide. Strong induction compares their first possible coefficient difference.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("General.exists_integral", "Integral solutions for multiples of a prime", IntegralFormula(),
                "For every prime p and every integer c divisible by p, the residual is coefficientwise divisible by p. Integer division supplies the correction, and triangular lifting produces a normalized integer solution.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The prime-exponent conjecture holds", Disp(ClaimBody()),
                "Taking c=p in the integral construction proves the conjecture for every prime exponent.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("hanna2016a271931-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name.Split('.')[^1]), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Rel(Formula a, Formula relation, Formula b) => Seq(a, Sp, relation, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Iffn(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Iff, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Ring(Formula body) => All("R", Named("Type"),
        Seq(OpenBracket, Call("CommRing", V("R")), CloseBracket, Comma, Sp, body));
    private static Formula Agreement(Formula n, Formula f, Formula g) =>
        All("k", N(), Imp(Rel(V("k"), Lt, n), Eqn(Call("coeff", V("k"), f), Call("coeff", V("k"), g))));
    private static Formula Inner(Formula p, Formula c, Formula f) =>
        Add(Pow(V("X"), p), Mul(Mul(Call("C", c), V("X")), Pow(f, p)));
    private static Formula Equation(Formula p, Formula c, Formula f) =>
        Eqn(Pow(f, p), App(Qualified("PowerSeries", "subst"), Inner(p, c, f), f));
    private static Formula ClaimBody() => All("p", N(), Imp(App(Qualified("Nat", "Prime"), V("p")),
        Ex("G", Series(Z()), And(Eqn(Call("constantCoeff", V("G")), D(0)), And(Eqn(Call("coeff", D(1), V("G")), D(1)), Eqn(Pow(V("G"), V("p")),
            App(Qualified("PowerSeries", "subst"), Add(Pow(V("X"), V("p")),
                Mul(Mul(Cast(V("p"), Series(Z())), V("X")), Pow(V("G"), V("p")))), V("G"))))))));
    private static Formula InnerFormula() => Disp(Ring(All("p", N(), All("c", V("R"),
        All("f", Series(V("R")), Eqn(App(Qualified("General", "inner"), V("p"), V("c"), V("f")),
            Inner(V("p"), V("c"), V("f"))))))));
    private static Formula IntegralFormula() => Disp(All("p", N(), Imp(App(Qualified("Nat", "Prime"), V("p")),
        All("c", Z(), Imp(Rel(Cast(V("p"), Z()), Mid, V("c")), Ex("G", Series(Z()),
            And(Eqn(Call("constantCoeff", V("G")), D(0)), And(Eqn(Call("coeff", D(1), V("G")), D(1)), Equation(V("p"), V("c"), V("G"))))))))));
    private static Formula UniqueFormula() => Disp(Ring(All("p", N(), Imp(Rel(D(2), Le, V("p")),
        All("c", V("R"), Seq(OpenBracket, Call("NoZeroDivisors", V("R")), CloseBracket, Comma, Sp,
            Imp(Rel(Cast(V("p"), V("R")), Neq, D(0)), All("f", Series(V("R")), All("g", Series(V("R")),
                Imp(Eqn(Call("constantCoeff", V("f")), D(0)), Imp(Eqn(Call("constantCoeff", V("g")), D(0)),
                Imp(Eqn(Call("coeff", D(1), V("f")), D(1)), Imp(Eqn(Call("coeff", D(1), V("g")), D(1)),
                Imp(Equation(V("p"), V("c"), V("f")), Imp(Equation(V("p"), V("c"), V("g")), Eqn(V("f"), V("g")))))))))))))))));
    private static Formula LiftingFormula() => Disp(Ring(
        All("F", Arr(Series(V("R")), Series(V("R"))), All("base", Series(V("R")),
        All("n0", N(), All("s", N(), All("a", V("R"), All("q", Arr(V("R"), V("R")),
            Imp(LiftingAgreement(), Imp(LiftingTop(), Imp(LiftingDivision(),
                Imp(Agreement(Add(V("n0"), V("s")), App(V("F"), V("base")), D(0)),
                    Ex("f", Series(V("R")), And(Agreement(V("n0"), V("f"), V("base")),
                        Eqn(App(V("F"), V("f")), D(0))))))))))))))));
    private static Formula LiftingAgreement() => All("n", N(), Imp(Rel(V("n0"), Le, V("n")),
        All("f", Series(V("R")), All("g", Series(V("R")),
            Imp(Agreement(V("n0"), V("f"), V("base")), Imp(Agreement(V("n0"), V("g"), V("base")),
            Imp(Agreement(V("n"), V("f"), V("g")), Agreement(Add(V("n"), V("s")),
                App(V("F"), V("f")), App(V("F"), V("g"))))))))));
    private static Formula LiftingTop() => All("n", N(), Imp(Rel(V("n0"), Le, V("n")),
        All("f", Series(V("R")), All("g", Series(V("R")),
            Imp(Agreement(V("n0"), V("f"), V("base")), Imp(Agreement(V("n0"), V("g"), V("base")),
            Imp(Agreement(V("n"), V("f"), V("g")), Eqn(
                Sub(Call("coeff", Add(V("n"), V("s")), App(V("F"), V("f"))),
                    Call("coeff", Add(V("n"), V("s")), App(V("F"), V("g")))),
                Mul(V("a"), Parenthesized(Sub(Call("coeff", V("n"), V("f")), Call("coeff", V("n"), V("g")))))))))))));
    private static Formula LiftingDivision() => All("f", Series(V("R")),
        Imp(Agreement(V("n0"), V("f"), V("base")), All("n", N(), Eqn(
            Mul(V("a"), App(V("q"), Call("coeff", V("n"), App(V("F"), V("f"))))),
            Seq(Minus, Call("coeff", V("n"), App(V("F"), V("f"))))))));
}
