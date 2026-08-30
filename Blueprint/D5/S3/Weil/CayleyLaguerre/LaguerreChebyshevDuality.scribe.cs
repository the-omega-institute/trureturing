using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class LaguerreChebyshevDualityDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/CayleyLaguerre/LaguerreChebyshevDuality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Laguerre time observation equals the Chebyshev derivative jet of one budget curve.",
        H("Laguerre-Chebyshev Duality"),
        Blocks(Describe.Lean(
            DescribeId.Create("laguerre-chebyshev-duality"),
            DeclarationHandle.Create(Handle + "laguerre_chebyshev_duality"),
            H("Laguerre-Chebyshev duality"),
            StatementSource.FromAuthor(DualityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The positive square scale constructs the resolvent-weighted measure. "
                    + "Finite-sum Laplace integration proves the time observation directly, "
                    + "and the scale-jet identity identifies its Cayley moment with the derivative sum."))),
            DescribeRole.Theorem))));

    private static Formula DualityFormula()
    {
        Formula real = Call("Real"), complex = Call("Complex");
        Formula natural = Call("Nat"), integer = Call("Int");
        Formula nu = F.Id("nu"), n = F.Id("n"), u = F.Id("u"), p = F.Id("p");
        Formula x = F.Id("x"), xi = F.Id("xi"), t = F.Id("t");
        Formula v = F.Id("v"), k = F.Id("k"), m = F.Id("m"), j = F.Id("j");
        Formula scale = F.Id("scale"), laguerreOne = F.Id("laguerreOne");
        Formula weighted = F.Id("weighted"), correlation = F.Id("correlation");
        Formula budget = F.Id("budget");
        Formula index = Call("Fin", Add(n, D(1)));
        Formula measure = Call("Measure", real);
        Formula coefficients = Arrow(index, real);

        Formula Budget(Formula argument) => Call(
            "integral",
            nu,
            Lambda(xi, Divide(D(1), Add(Pow(xi, D(2)), argument))));
        Formula LaguerreOne(Formula order, Formula argument) => Call(
            "sum",
            Call("range", Add(order, D(1))),
            Lambda(j, Mul(
                Divide(
                    Mul(
                        Pow(Neg(D(1)), j),
                        Call("choose", Add(order, D(1)), Add(j, D(1)))),
                    Call("factorial", j)),
                Pow(argument, j))));
        Formula density = Lambda(xi, Call(
            "ofReal",
            Call("inv", Add(Pow(xi, D(2)), Pow(scale, D(2))))));
        Formula Correlation(Formula argument) => Integral(
            xi,
            real,
            Call("exp", Mul(Mul(Call("I"), argument), xi)),
            weighted);
        Formula coefficientExpansion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", real)],
            Equal(
                Call("ChebyshevT", integer, n, Sub(D(1), Mul(D(2), x))),
                Call("sum", index, Lambda(k, Mul(Apply(p, k), Pow(x, k))))));
        Formula assumptions = All(
            Equal(Call("map", Lambda(xi, Neg(xi)), nu), nu),
            LessEqual(D(1), n),
            Less(D(0), u),
            coefficientExpansion,
            Call("Integrable", Lambda(xi, Divide(D(1), Add(Pow(xi, D(2)), u))), nu));

        Formula correlationIntegral = Integral(
            t,
            real,
            Mul(
                    Call("complex", Mul(
                        Call("exp", Neg(Mul(scale, t))),
                        Apply(laguerreOne, Sub(n, D(1)), Mul(Mul(D(2), scale), t)))),
                Apply(correlation, t)),
            Call("restrict", Call("volume"), Call("Ioi", D(0))));
        Formula timeObservation = Sub(
            Call("complex", Apply(budget, u)),
            Mul(Call("complex", Mul(D(2), scale)), correlationIntegral));
        Formula derivative = Call("iteratedDeriv", k, budget, u);
        Formula jet = Call("complex", Call("sum", index, Lambda(k,
            Mul(
                Mul(
                    Mul(Apply(p, k), Pow(u, k)),
                    Divide(Pow(Neg(D(1)), k), Call("factorial", k))),
                derivative))));
        Formula definitions = Seq(
            F.Id("let"), Sp, Typed(scale, real), Sp, Eq, Sp, Call("sqrt", u), Semi, Sp,
            F.Id("let"), Sp, Typed(laguerreOne, Arrow(natural, Arrow(real, real))), Sp, Eq, Sp,
            Lambda(m, Lambda(x, LaguerreOne(m, x))), Semi, Sp,
            F.Id("let"), Sp, Typed(weighted, measure), Sp, Eq, Sp,
            Call("withDensity", nu, density), Semi, Sp,
            F.Id("let"), Sp, Typed(correlation, Arrow(real, complex)), Sp, Eq, Sp,
            Lambda(t, Correlation(t)), Semi, Sp,
            F.Id("let"), Sp, Typed(budget, Arrow(real, real)), Sp, Eq, Sp,
            Lambda(v, Budget(v)), Semi, Sp,
            Equal(timeObservation, jet));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("nu", measure),
                Bound("n", natural),
                Bound("u", real),
                Bound("p", coefficients),
            ],
            Implies(assumptions, definitions)));
    }

    private static Formula Integral(
        Formula variable, Formula domain, Formula integrand, Formula measure) =>
        Call("integral", variable, domain, integrand, measure);

    private static Formula Lambda(Formula variable, Formula body) =>
        Call("lambda", variable, body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Pow(Formula value, Formula exponent) =>
        Call("pow", value, exponent);

    private static Formula Neg(Formula value) => Call("neg", value);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }
}
