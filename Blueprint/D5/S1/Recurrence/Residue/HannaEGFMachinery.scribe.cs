using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class HannaEGFMachineryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/HannaEGFMachinery.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral derivative-substitution recurrences transfer exact residual divisibility to all coefficients.",
        H("Integral EGF recurrences and residual transfer"),
        Blocks(
            Paragraph(Text("All series below are rational formal power series. The existing eCoeff(F,n) is n! times coeff(n,F), "
                + "and Integral(F) means that these coefficients are integers. The binomial convolution and its powers "
                + "are taken from ExponentialImplicitParityPeriodThree. No analytic convergence is asserted.")),
            Node("sourceRhs", "Derivative-substitution operator", SourceDefinition(),
                "For a rational formal series f, natural k and p, and Boolean r, the true branch uses the inverse derivative. The false branch uses its kth power. Substitution precedes the pth power.", DescribeRole.Definition),
            Node("Multiple", "Divisibility of all exponential coefficients", MultipleDefinition(),
                "Multiple(m,F) means that each factorial-normalized rational coefficient of F is m times an integer. Both integer witnesses and the natural modulus are cast into Rat.", DescribeRole.Definition),
            Node("residual_transfer", "Transfer from a divisible residual", Transfer(),
                "An integral approximate solution and an exact solution with constant coefficient one have the same exponential coefficients modulo m when the derivative-substitution residual is divisible by m. The reciprocal branch also requires derivative constant coefficient one for the approximate solution.", DescribeRole.Theorem),
            Node("integral_derivative", "Differentiation preserves integrality", All("F", PS(), Imp(Call("Integral", V("F")), Call("Integral", Der(V("F"))))),
                "Integral(F) is the existing predicate that every eCoeff(F,n) is an integer. This implication holds for all rational formal series under the displayed hypotheses.", DescribeRole.Theorem),
            Node("integral_pow", "Powers preserve integrality", All("F", PS(), All("k", N(), Imp(Call("Integral", V("F")), Call("Integral", Pow(V("F"), V("k")))))),
                "Integral(F) is the existing predicate that every eCoeff(F,n) is an integer. This implication holds for all rational formal series under the displayed hypotheses.", DescribeRole.Theorem),
            Node("integral_X_mul", "Multiplication by X preserves integrality", All("F", PS(), Imp(Call("Integral", V("F")), Call("Integral", Multiply(V("X"), V("F"))))),
                "Integral(F) is the existing predicate that every eCoeff(F,n) is an integer. This implication holds for all rational formal series under the displayed hypotheses.", DescribeRole.Theorem),
            Node("integral_inv", "Normalized inversion preserves integrality", All("F", PS(), Imp(Call("Integral", V("F")), Imp(Equal(Call("constantCoeff", V("F")), Num(1)), Call("Integral", App(Qualified("Inv", "inv"), V("F")))))),
                "Integral(F) is the existing predicate that every eCoeff(F,n) is an integer. This implication holds for all rational formal series under the displayed hypotheses.", DescribeRole.Theorem),
            Node("integral_sub", "Subtraction preserves integrality", All("F", PS(), All("G", PS(), Imp(Call("Integral", V("F")), Imp(Call("Integral", V("G")), Call("Integral", Subtract(V("F"), V("G"))))))),
                "Subtract the integer witnesses of the two factorial-normalized coefficients.", DescribeRole.Theorem),
            Node("multiple_cancel", "Cancellation of an integral unit", Cancellation(),
                "In binomial convolution the degree-n term of the unknown sequence has coefficient one. Induction therefore cancels an integral series with constant coefficient one modulo every natural modulus.", DescribeRole.Theorem),
            Node("finite_multiple", "Finite certificates imply all-degree divisibility", FiniteCertificate(),
                "Each list entry is checked after multiplying by its index factorial. Beyond the list length the coefficient vanishes. The notation a[n]! is Lean list indexing with the default value outside the list.", DescribeRole.Theorem),
            Node("clear_inverse_power", "Clearing powers of a normalized inverse", ClearInverse(),
                "When j is at most n, multiplication by U to the nth power clears all j inverse factors. The subtraction n-j is natural subtraction.", DescribeRole.Theorem),
            Node("expSum", "The exponential composition coefficient sum", ExpSumDefinition(),
                "This integer binomial sum is the factorial-normalized coefficient of exp(X exp(k X)). Every index is natural; the inner casts and the exponent are displayed explicitly.", DescribeRole.Definition),
            Node("expSum_mod", "Every divisor of k gives a unit residue", All("k", N(), All("m", N(), All("n", N(), Imp(Dvd(V("m"), V("k")), Dvd(Cast(V("m"), Z()), Subtract(Call("expSum", V("k"), V("n")), Num(1))))))),
                "The terminal term is one and each earlier term contains a positive power of a multiple of m.", DescribeRole.Theorem),
            Node("expSum_four_mod_eight", "The fourth-power exponential coefficient is one modulo eight", All("n", N(), Dvd(Cast(Num(8), Z()), Subtract(Call("expSum", Num(4), V("n")), Num(1)))),
                "The penultimate term is 4 n (n-1), divisible by eight; each earlier term contains a square of a multiple of four.", DescribeRole.Theorem),
            Node("exp_residual", "A binomial-sum residue controls the exponential residual", ExponentialResidual(),
                "Every exponential coefficient of the derivative of exp is one. Subtracting the computed composition coefficient converts the integer divisibility into the stated rational residual identity.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hanna-egf-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula SourceDefinition()
    {
        var f = V("f"); var k = V("k"); var p = V("p"); var r = V("r");
        var inner = Multiply(V("X"), Call("ite", Equal(r, V("true")),
            App(Qualified("Inv", "inv"), Der(f)), Pow(Der(f), k)));
        return All("f", PS(), All("k", N(), All("p", N(), All("r", V("Bool"),
            Equal(Call("sourceRhs", f, k, p, r), Pow(App(Qualified("PowerSeries", "subst"), f, inner), p))))));
    }

    private static Formula MultipleBody(Formula m, Formula f) =>
        All("n", N(), Ex("z", Z(), Equal(Coeff(f, V("n")), Multiply(Cast(m, Q()), Cast(V("z"), Q())))));

    private static Formula MultipleDefinition() => All("m", N(), All("F", PS(),
        Iff(Call("Multiple", V("m"), V("F")), MultipleBody(V("m"), V("F")))));

    private static Formula Transfer()
    {
        var a = V("A"); var f = V("F"); var k = V("k"); var p = V("p"); var m = V("m"); var r = V("r");
        var n = V("n");
        var he = Equal(Der(a), Call("sourceRhs", a, k, p, r));
        var hf = All("n", N(), Equal(Coeff(f, n), Cast(App(V("f"), n), Q())));
        var hf1 = Imp(Equal(r, V("true")), Equal(Call("constantCoeff", Der(f)), Num(1)));
        var hr = MultipleBody(m, Subtract(Der(f), Call("sourceRhs", f, k, p, r)));
        var conclusion = Ex("a", Arr(N(), Z()), And(
            All("n", N(), Equal(Coeff(a, n), Cast(App(V("a"), n), Q()))),
            All("n", N(), Dvd(Cast(m, Z()), Subtract(App(V("a"), n), App(V("f"), n))))));
        return All("A", PS(), All("F", PS(), All("k", N(), All("p", N(), All("m", N(), All("r", V("Bool"),
            Imp(Equal(Call("constantCoeff", a), Num(1)), Imp(he, All("f", Arr(N(), Z()),
                Imp(hf, Imp(Equal(App(V("f"), Num(0)), Num(1)), Imp(hf1, Imp(hr, conclusion)))))))))))));
    }

    private static Formula Cancellation() => All("U", PS(), All("V", PS(), All("m", N(),
        Imp(Call("Integral", V("U")), Imp(Call("Integral", V("V")),
            Imp(Equal(Call("constantCoeff", V("U")), Num(1)),
                Imp(Call("Multiple", V("m"), Multiply(V("U"), V("V"))), Call("Multiple", V("m"), V("V")))))))));

    private static Formula Index(Formula a, Formula n) => Seq(a, OpenBracket, n, CloseBracket, Bang);
    private static Formula FiniteCertificate()
    {
        var a = V("a"); var z = V("z"); var m = V("m"); var n = V("n"); var val = Call("val", n);
        var he = All("n", Call("Fin", App(Qualified("List", "length"), a)),
            Equal(Multiply(Cast(App(Qualified("Nat", "factorial"), val), Q()), Index(a, val)),
                Multiply(Cast(m, Q()), Cast(Index(z, val), Q()))));
        return All("a", Call("List", Q()), All("z", Call("List", Z()), All("m", N(),
            Imp(he, Call("Multiple", m, Cast(App(Qualified("Polynomial", "ofCoeffList"), a), PS()))))));
    }

    private static Formula ClearInverse()
    {
        var u = V("U"); var n = V("n"); var j = V("j");
        return All("U", PS(), Imp(Equal(Call("constantCoeff", u), Num(1)), All("n", N(), All("j", N(),
            Imp(Leq(j, n), Equal(Multiply(Pow(u, n), Pow(Multiply(V("X"), App(Qualified("Inv", "inv"), u)), j)),
                Multiply(Pow(V("X"), j), Pow(u, Subtract(n, j)))))))));
    }

    private static Formula ExpSumDefinition()
    {
        var k = V("k"); var n = V("n"); var j = V("j");
        var summand = Multiply(Cast(App(Qualified("Nat", "choose"), n, j), Z()),
            Pow(Cast(Multiply(k, j), Z()), Subtract(n, j)));
        var sum = Seq(new Formula.Subscript(Sum, Grp(j, Sp, InMacro, Sp,
            App(Qualified("Finset", "range"), Add(n, Num(1))))), Sp, summand);
        return All("k", N(), All("n", N(), Equal(Call("expSum", k, n), sum)));
    }

    private static Formula ExponentialResidual()
    {
        var k = V("k"); var m = V("m"); var n = V("n"); var exp = App(Qualified("PowerSeries", "exp"), Q());
        var h = All("n", N(), Dvd(Cast(m, Z()), Subtract(Call("expSum", k, n), Num(1))));
        var residual = Subtract(Der(exp), App(Qualified("PowerSeries", "subst"), exp,
            Multiply(V("X"), Pow(Der(exp), k))));
        return All("k", N(), All("m", N(), Imp(h, MultipleBody(m, residual))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS() => Call("PowerSeries", Q());
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Pow(Formula f, Formula n) => new Formula.Power(f, n);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Dvd(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula All(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Ex(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Der(Formula a) => App(Qualified("PowerSeries", "derivative"), a);
    private static Formula Coeff(Formula a, Formula n) => Call("eCoeff", a, n);
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
}
