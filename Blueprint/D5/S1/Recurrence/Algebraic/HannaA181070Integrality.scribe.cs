using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA181070IntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA181070Integrality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2010a181070family");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer coefficients of Hanna's OEIS A181070 formal exponential.",
        H("Hanna A181070 Integrality"), Blocks(
            Node("logarithm", "The rational logarithm", Eqn(Call("logarithm"), Qualified("PowerSeries", "mk", Lam("m", N(), DiagonalSum(true, Pow(Cast(Choose(V("n"), V("k")), Q()), Add(V("k"), D(1))))))),
                "OEIS A181070, NAME (web entry, no page number): \"Expansion of G.f.: A(x) = exp( Sum_{n>=1} (Sum_{k=0..n} C(n,k)^(k+1)*x^k)*x^n/n ).\" The displayed coefficient formula collects the terms of degree m. The indices and all subtractions are natural numbers; subtraction is truncated at zero. The binomial coefficient is Nat.choose.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A", "The formal exponential", Eqn(Call("A"), ExpOf(Call("logarithm"))),
                "OEIS A181070, NAME (web entry, no page number): \"Expansion of G.f.: A(x) = exp( Sum_{n>=1} (Sum_{k=0..n} C(n,k)^(k+1)*x^k)*x^n/n ).\" The exponential is formal over the rationals. PowerSeries.subst takes the inner series as its first argument.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Integer coefficients", Iffn(Call("claim"), ClaimBody()),
                "OEIS A181070, first COMMENTS line (web entry, no page number): \"Conjecture: this sequence consists entirely of integers.\" The degree m ranges over all natural numbers, including zero; the integer z may depend on m.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coeffLift", "Lifting coefficients along prime scaling", All("U", PS(Z()), All("p", N(), All("n", N(), All("k", N(), Imp(Prime(V("p")), Divides(Pow(Cast(V("p"), Z()), Add(Val(V("p"), V("n")), D(1))), Sub(Coeff(Mul(V("p"), V("k")), Pow(V("U"), Mul(V("p"), V("n")))), Coeff(V("k"), Pow(V("U"), V("n")))))))))),
                "Prime-power lifting of a series power compares coefficients at k and p times k.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("variableExponent", "The variable exponent congruence", All("p", N(), All("n", N(), All("k", N(), All("b", N(), Imp(Prime(V("p")), Imp(Divides(V("n"), Mul(V("k"), V("b"))), ModEqn(Pow(V("p"), Add(Val(V("p"), V("n")), D(1))), Pow(V("b"), Add(Mul(V("p"), V("k")), D(1))), Pow(V("b"), Add(V("k"), D(1)))))))))),
                "For bases coprime to p, Euler's theorem changes the exponent. For bases divisible by p, the divisibility assumption makes both powers vanish modulo the stated prime power.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("L", "A diagonal rational series", All("F", ArrayType(), Eqn(Call("L", V("F")), Qualified("PowerSeries", "mk", Lam("m", N(), RangeSum("n", Add(V("m"), D(1)), new Formula.Fraction(Cast(ApplyF(V("n"), Sub(V("m"), V("n"))), Q()), Cast(V("n"), Q()))))))),
                "The coefficient in degree m is the finite diagonal sum of F(n,m-n)/n. Subtraction takes place in the natural numbers and division takes place in the rationals.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("integralGeneric", "A sufficient array criterion", All("F", ArrayType(), Imp(DivisibilityBody(), Imp(CongruenceBody(), IntegralBody(ExpOf(Call("L", V("F"))))))),
                "The weighted diagonal with weight n+k satisfies Dold congruences. The Dold exponential integrality criterion then supplies an integer for each coefficient.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("coefficientDivisibility", "Divisibility of coefficients of powers", All("U", PS(Z()), All("n", N(), All("k", N(), Divides(Cast(V("n"), Z()), Mul(Cast(V("k"), Z()), Coeff(V("k"), Pow(V("U"), V("n")))))))),
                "Differentiating a power expresses k times its coefficient as n times a coefficient of the derivative product.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("binomDiv", "Binomial coefficient divisibility", All("n", N(), All("k", N(), Divides(V("n"), Mul(V("k"), Choose(V("n"), V("k")))))),
                "Coefficient divisibility for the power of 1+X makes k times Nat.choose n k a multiple of n.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("binomCong", "Binomial coefficient congruence", All("p", N(), All("n", N(), All("k", N(), Imp(Prime(V("p")), ModEqn(Pow(V("p"), Add(Val(V("p"), V("n")), D(1))), Choose(Mul(V("p"), V("n")), Mul(V("p"), V("k"))), Choose(V("n"), V("k"))))))),
                "Coefficient lifting applied to the power series 1+X gives the binomial congruence.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("divPower", "Divisibility survives positive powers", DivPowerFormula(),
                "Multiplication by further powers preserves the original divisibility.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("literalUnbounded", "Collecting an unbounded inner sum", All("F", ArrayType(), All("m", N(), Eqn(DiagonalSum(false, Cast(ApplyF(V("n"), V("k")), Q())), Coeff(V("m"), Call("L", V("F")))))),
                "For a fixed degree, the equation n+k=m selects exactly one inner index. The zero outer index contributes zero by rational division.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("literalBounded", "Collecting a bounded inner sum", All("F", ArrayType(), Imp(All("n", N(), All("k", N(), Imp(Lt(V("n"), V("k")), Eqn(ApplyF(V("n"), V("k")), D(0))))), All("m", N(), Eqn(DiagonalSum(true, Cast(ApplyF(V("n"), V("k")), Q())), Coeff(V("m"), Call("L", V("F"))))))),
                "If the array vanishes above k=n, restricting the inner sum to k at most n leaves every coefficient unchanged.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "Integrality in every degree", ClaimBody(),
                "Every coefficient of the displayed formal exponential is an integer. The prime-scaling congruence and diagonal identity reduce the assertion to the Dold exponential integrality criterion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hannaa181070-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS(Formula ring) => Call("PowerSeries", ring);
    private static Formula ArrayType() => Seq(N(), Sp, To, Sp, N(), Sp, To, Sp, N());
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Divides(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Iffn(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Iff, Sp, Parenthesized(b));
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Coeff(Formula n, Formula a) => Qualified("PowerSeries", "coeff", n, a);
    private static Formula Choose(Formula n, Formula k) => Qualified("Nat", "choose", n, k);
    private static Formula ExpOf(Formula f) => Qualified("PowerSeries", "subst", f, Qualified("PowerSeries", "exp", Q()));
    private static Formula Val(Formula p, Formula n) => Call("padicValNat", p, n);
    private static Formula Prime(Formula p) => Qualified("Nat", "Prime", p);
    private static Formula ModEqn(Formula q, Formula a, Formula b) => Qualified("Nat", "ModEq", q, a, b);
    private static Formula ApplyF(Formula n, Formula k) => new Formula.Apply(V("F"), [n, k]);
    private static Formula RangeSum(string index, Formula bound, Formula body) =>
        Qualified("Finset", "sum", Qualified("Finset", "range", bound), Lam(index, N(), body));
    private static Formula DiagonalSum(bool bounded, Formula value)
    {
        var n = V("n"); var k = V("k"); var m = V("m");
        var condition = And(Lt(D(0), n), Eqn(Add(n, k), m));
        var summand = Seq(V("if"), Sp, Parenthesized(condition), Sp, V("then"), Sp,
            new Formula.Fraction(value, Cast(n, Q())), Sp, V("else"), Sp, D(0));
        return RangeSum("n", Add(m, D(1)), RangeSum("k", Add(bounded ? n : m, D(1)), summand));
    }
    private static Formula ClaimBody() => All("m", N(), Ex("z", Z(), Eqn(Coeff(V("m"), Call("A")), Cast(V("z"), Q()))));
    private static Formula IntegralBody(Formula series) => All("m", N(), Ex("z", Z(), Eqn(Coeff(V("m"), series), Cast(V("z"), Q()))));
    private static Formula DivisibilityBody() => All("n", N(), All("k", N(), Imp(Ne(V("n"), D(0)),
        Divides(V("n"), Mul(V("k"), ApplyF(V("n"), V("k")))))));
    private static Formula CongruenceBody() => All("p", N(), Imp(Prime(V("p")), All("n", N(), All("k", N(),
        Imp(Ne(V("n"), D(0)), Divides(Pow(Cast(V("p"), Z()), Add(Val(V("p"), V("n")), D(1))),
            Sub(Cast(ApplyF(Mul(V("p"), V("n")), Mul(V("p"), V("k"))), Z()), Cast(ApplyF(V("n"), V("k")), Z()))))))));
    private static Formula DivPowerFormula()
    {
        var n = V("n"); var k = V("k");
        var value = new Formula.Apply(V("B"), [n, k]);
        var exponent = new Formula.Apply(V("e"), [n, k]);
        var premise = All("n", N(), All("k", N(),
            Imp(Ne(n, D(0)), Divides(n, Mul(k, value)))));
        var conclusion = All("n", N(), All("k", N(),
            Imp(Ne(n, D(0)), Divides(n, Mul(k, Pow(value, Add(exponent, D(1))))))));
        return All("B", ArrayType(), All("e", ArrayType(), Imp(premise, conclusion)));
    }
}
