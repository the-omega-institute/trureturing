using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class DoldExponentialIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/aintlib2026dieudonnedwork");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dold prime-power congruences imply integrality of a formal exponential.",
        H("Dold Congruences and Formal Exponential Integrality"),
        Blocks(
            Node("IsRIntegralRat", "Rational coefficients with coprime denominator",
                All("r", N(), All("q", Q(), Seq(Call("IsRIntegralRat", V("r"), V("q")), Sp, Iff, Sp,
                    QualifiedCall("Nat", "Coprime", QualifiedCall("Rat", "den", V("q")), V("r"))))),
                "The reduced positive denominator of q is coprime to r.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("IsRIntegralRat.zero", "Zero has coprime denominator",
                All("r", N(), Call("IsRIntegralRat", V("r"), D(0))),
                "Zero has denominator one.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("IsRIntegralRat.one_coprime", "One has coprime denominator",
                All("r", N(), Call("IsRIntegralRat", V("r"), D(1))),
                "One has denominator one.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("IsRIntegralRat.add", "Addition preserves coprime denominators",
                LocalClosure(false), "The denominator of a sum divides the product of the denominators.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("IsRIntegralRat.neg", "Negation preserves coprime denominators",
                All("r", N(), All("q", Q(), Imp(Call("IsRIntegralRat", V("r"), V("q")),
                    Call("IsRIntegralRat", V("r"), new Formula.Negate(V("q")))))),
                "Negation preserves the reduced denominator.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("IsRIntegralRat.mul_coprime", "Multiplication preserves coprime denominators",
                LocalClosure(true), "The denominator of a product divides the product of the denominators.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("expSeries_derivative", "Derivative of a substituted exponential",
                All("h", PS(Q()), Imp(Eqn(Call("constantCoeff", V("h")), D(0)),
                    Eqn(Call("derivative", Exponential(V("h"))),
                        Mul(Exponential(V("h")), Call("derivative", V("h")))))),
                "Formal differentiation of exp(h) gives exp(h) times the derivative of h.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("IsRIntegralPS", "Coefficientwise local integrality",
                All("r", N(), All("f", PS(Q()), Eqn(Call("IsRIntegralPS", V("r"), V("f")),
                    All("n", N(), Call("IsRIntegralRat", V("r"), Coeff(V("n"), V("f"))))))),
                "Every coefficient has denominator coprime to r.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("local_integral_sum", "Finite sums preserve local integrality", LocalSumFormula(),
                "A finite sum of rationals with denominators coprime to r again has denominator coprime to r.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("expSeries_constant", "The formal exponential has constant one",
                All("h", PS(Q()), Imp(Eqn(Call("constantCoeff", V("h")), D(0)),
                    Eqn(Call("constantCoeff", Exponential(V("h"))), D(1)))),
                "A zero-constant formal input gives constant coefficient one after exponential substitution.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("integral_of_local", "Local integrality at all primes is integral",
                All("f", PS(Q()), Imp(All("p", N(), Imp(QualifiedCall("Nat", "Prime", V("p")),
                    Call("IsRIntegralPS", V("p"), V("f")))),
                    QualifiedCall("HannaLogarithmicPowerClosure", "IntegralSeries", V("f")))),
                "A rational denominator coprime to every prime equals one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("local_exp_of_log_difference", "The sufficient Dieudonne-Dwork criterion",
                LocalExponentialFormula(),
                "For each prime p, local integrality of h-p inverse times h(X^p) implies local integrality of exp(h). The input h has constant coefficient zero.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("local_int_div_nat", "Cancelling a natural denominator locally",
                LocalQuotientFormula(),
                "If p to the valuation of nonzero n divides the integer z, then z/n has denominator coprime to p.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("Dold", "Prime-power congruences", All("c", Seq(N(), Sp, To, Sp, Z()), Seq(Call("Dold", V("c")), Sp, Iff, Sp, P(DoldBody()))),
                "Dold(c) requires divisibility by p to the valuation of m plus one for every prime p and every nonzero natural m.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("logInput", "The rational logarithmic input", All("c", Seq(N(), Sp, To, Sp, Z()), Eqn(Call("logInput", V("c")), Call("mk", Lam("n", N(), new Formula.Fraction(Cast(new Formula.Apply(V("c"), [V("n")]), Q()), Cast(V("n"), Q())))))),
                "The degree-n input coefficient is c(n)/n over the rationals; rational division makes the constant coefficient zero.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("expSeries_nsmul", "Scaling the input takes powers", All("f", PS(Q()), Imp(Eqn(Call("constantCoeff", V("f")), D(0)), All("n", N(), Eqn(Exponential(QualifiedCall("HSMul", "hSMul", V("n"), V("f"))), Pow(Exponential(V("f")), V("n")))))),
                "Substitution into PowerSeries.exp_pow_eq_rescale_exp gives the natural-scaling identity.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)),
            Node("expSeries_add", "Exponential of a sum", ExponentialAdditionFormula(),
                "For two rational formal series with zero constant coefficients, substituting their sum "
                    + "into the exponential gives the product of the two substituted exponentials.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("integral_exp_of_dold", "Dold congruences imply integrality", All("c", Seq(N(), Sp, To, Sp, Z()), Imp(Call("Dold", V("c")), All("n", N(), Ex("z", Z(), Eqn(Coeff(V("n"), Exponential(Call("logInput", V("c")))), Cast(V("z"), Q())))))),
                "Apply the sufficient Dieudonne-Dwork criterion at each prime. The Dold congruences make the logarithmic difference locally integral; a rational coefficient integral at every prime has denominator one. The local-integrality induction is adapted from AINTLIB.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source)))));

    private static Formula LocalSumFormula()
    {
        var f = V("f"); var s = V("s"); var r = V("r");
        var premise = All("i", V("I"), Imp(Seq(V("i"), Sp, InMacro, Sp, s),
            Call("IsRIntegralRat", r, new Formula.Apply(f, [V("i")]))));
        var sum = QualifiedCall("Finset", "sum", s,
            Lam("i", V("I"), new Formula.Apply(f, [V("i")])));
        return All("r", N(), All("I", Seq(V("Type"), Star),
            All("s", Call("Finset", V("I")), All("f", Seq(V("I"), Sp, To, Sp, Q()),
                Imp(premise, Call("IsRIntegralRat", r, sum))))));
    }

    private static Formula LocalExponentialFormula()
    {
        var p = V("p"); var h = V("h");
        var substituted = Call("subst", Pow(V("X"), p), h);
        var difference = new Formula.Binary(h, FormulaBinaryOperator.Subtract,
            Mul(Call("C", QualifiedCall("Inv", "inv", Cast(p, Q()))), substituted));
        return All("p", N(), Imp(QualifiedCall("Nat", "Prime", p),
            All("h", PS(Q()), Imp(Eqn(Call("constantCoeff", h), D(0)),
                Imp(Call("IsRIntegralPS", p, difference),
                    Call("IsRIntegralPS", p, Exponential(h)))))));
    }

    private static Formula LocalQuotientFormula()
    {
        var p = V("p"); var n = V("n"); var z = V("z");
        var divides = Seq(Pow(Cast(p, Z()), Call("padicValNat", p, n)), Sp, Mid, Sp, z);
        return All("p", N(), Imp(QualifiedCall("Nat", "Prime", p),
            All("z", Z(), All("n", N(), Imp(Seq(n, Sp, Neq, Sp, D(0)),
                Imp(divides, Call("IsRIntegralRat", p,
                    new Formula.Fraction(Cast(z, Q()), Cast(n, Q())))))))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("doldexponentialintegrality-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula P(Formula value) => Parenthesized(value);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS(Formula ring) => Call("PowerSeries", ring);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Cast(Formula a, Formula type) => P(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(P(a), Sp, Implies, Sp, P(b));
    private static Formula Lam(string name, Formula type, Formula body) =>
        P(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Coeff(Formula n, Formula series) => Call("coeff", n, series);
    private static Formula DoldBody()
    {
        var p = V("p"); var m = V("m"); var c = V("c");
        var difference = new Formula.Binary(new Formula.Apply(c, [Mul(p, m)]),
            FormulaBinaryOperator.Subtract, new Formula.Apply(c, [m]));
        var divides = Seq(Pow(Cast(p, Z()), Add(Call("padicValNat", p, m), D(1))),
            Sp, Mid, Sp, P(difference));
        var nonzero = Seq(m, Sp, Neq, Sp, D(0));
        return All("p", N(), Imp(QualifiedCall("Nat", "Prime", p),
            All("m", N(), Imp(nonzero, divides))));
    }
    private static Formula QualifiedCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Exponential(Formula input) => Call("subst", input, Call("exp", Q()));
    private static Formula LocalClosure(bool product)
    {
        var r = V("r"); var a = V("q1"); var b = V("q2");
        var value = product ? Mul(a, b) : Add(a, b);
        return All("r", N(), All("q1", Q(), All("q2", Q(),
            Imp(Call("IsRIntegralRat", r, a), Imp(Call("IsRIntegralRat", r, b),
                Call("IsRIntegralRat", r, value))))));
    }
    private static Formula ExponentialAdditionFormula()
    {
        var f = V("f"); var g = V("g");
        return All("f", PS(Q()), All("g", PS(Q()),
            Imp(Eqn(Call("constantCoeff", f), D(0)),
                Imp(Eqn(Call("constantCoeff", g), D(0)),
                    Eqn(Exponential(Add(f, g)), Mul(Exponential(f), Exponential(g)))))));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);



}
