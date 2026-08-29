using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class CayleyMomentTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/CayleyLaguerre/CayleyMomentTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cayley moments have a finite derivative jet and a geometric scale-transport tail bound.",
        H("Cayley Moment Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("chebyshev-stieltjes-jet"),
                DeclarationHandle.Create(Prefix + "chebyshev_stieltjes_jet"),
                H("Chebyshev-Stieltjes jet"),
                StatementSource.FromAuthor(ChebyshevJetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The even measure, positive square scale, coefficient family, "
                            + "polynomial identity, and resolvent integrability condition at "
                            + "that scale are all displayed.")),
                    Paragraph(Text(
                        "Evenness identifies the full complex Cayley moment with its real "
                            + "part; the proof then uses the shifted Chebyshev polynomial and "
                            + "differentiates under a locally dominated integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("budget-transport-error"),
                DeclarationHandle.Create(Prefix + "budget_transport_error"),
                H("Budget transport error"),
                StatementSource.FromAuthor(BudgetTransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two positive scales, truncation order, even measure, and "
                            + "resolvent integrability premise are displayed explicitly.")),
                    Paragraph(Text(
                        "The proof expands every moment from the Cayley coordinate, reduces "
                            + "scale transport to the Poisson kernel, and integrates its "
                            + "finite geometric remainder."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Call("lambda", Call("typed", variable, domain), body);

    private static Formula Add(Formula left, Formula right) => Call("add", left, right);

    private static Formula Subtract(Formula left, Formula right) => Call("sub", left, right);

    private static Formula Multiply(params Formula[] factors) => Call("mul", factors);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Power(Formula value, Formula exponent) =>
        Call("pow", value, exponent);

    private static Formula Negate(Formula value) => Call("neg", value);

    private static Formula ChebyshevJetFormula()
    {
        Formula real = Call("Real"), natural = Call("Nat"), integer = Call("Int");
        Formula nu = F.Id("nu"), n = F.Id("n"), u = F.Id("u"), p = F.Id("p");
        Formula x = F.Id("x"), xi = F.Id("xi"), v = F.Id("v"), k = F.Id("k");
        Formula index = Call("Fin", Add(n, D(1)));
        Formula measure = Call("Measure", real);
        Formula coefficients = new Formula.TypeArrow(index, real);
        Formula P(Formula value) => Call("ChebyshevT", integer, n,
            Subtract(D(1), Multiply(D(2), value)));
        Formula Budget(Formula scale) => Call("integral", nu,
            Lambda(xi, real, Divide(D(1), Add(Power(xi, D(2)), scale))));
        Formula Derivative(Formula order) =>
            Call("iteratedDeriv", order, Lambda(v, real, Budget(v)), u);
        Formula coefficientExpansion = ForAll(
            [Bound("x", real)],
            Equal(
                P(x),
                Call("sum", index, Lambda(k, index,
                    Multiply(Apply(p, k), Power(x, k))))));
        Formula integrability = Call("Integrable", Lambda(xi, real,
            Divide(D(1), Add(Power(xi, D(2)), u))), nu);
        Formula evenness = Equal(
            Call("map", Lambda(xi, real, Negate(xi)), nu), nu);
        Formula scale = Call("sqrt", u);
        Formula cayley = Divide(
            Add(Call("ofReal", xi), Multiply(Call("I"), scale)),
            Subtract(Call("ofReal", xi), Multiply(Call("I"), scale)));
        Formula moment = Call("integral", nu, Lambda(xi, real,
            Divide(Power(cayley, n),
                Add(Power(xi, D(2)), u))));
        Formula jet = Call("ofReal", Call("sum", index, Lambda(k, index,
            Multiply(
                Apply(p, k),
                Power(u, k),
                Divide(Power(Negate(D(1)), k), Call("factorial", k)),
                Derivative(k)))));

        Formula assumptions = All(
            evenness,
            Less(D(0), u),
            coefficientExpansion,
            integrability);

        return F.Disp(ForAll(
            [
                Bound("nu", measure),
                Bound("n", natural),
                Bound("u", real),
                Bound("p", coefficients),
            ],
            Implies(assumptions, Equal(moment, jet))));
    }

    private static Formula BudgetTransportFormula()
    {
        Formula real = Call("Real"), natural = Call("Nat");
        Formula nu = F.Id("nu"), a = F.Id("a"), b = F.Id("b"), m = F.Id("M");
        Formula xi = F.Id("xi"), k = F.Id("k");
        Formula measure = Call("Measure", real);
        Formula denominator(Formula scale) =>
            Add(Power(xi, D(2)), Power(scale, D(2)));
        Formula budgetIntegrand(Formula scale) =>
            Divide(D(1), denominator(scale));
        Formula budget(Formula scale) => Call("integral", nu,
            Lambda(xi, real, budgetIntegrand(scale)));
        Formula complexBudget(Formula scale) => Call("ofReal", budget(scale));
        Formula r = Divide(Subtract(a, b), Add(a, b));
        Formula cayley = Divide(
            Add(Call("ofReal", xi), Multiply(Call("I"), a)),
            Subtract(Call("ofReal", xi), Multiply(Call("I"), a)));
        Formula momentIntegrand(Formula order) => Divide(
            Power(cayley, order), denominator(a));
        Formula moment(Formula order) => Call("integral", nu,
            Lambda(xi, real, momentIntegrand(order)));
        Formula order = Add(k, D(1));
        Formula finiteTransport = Add(
            complexBudget(a),
            Multiply(D(2), Call("sum", Call("range", m),
                Lambda(k, natural,
                    Multiply(Call("ofReal", Power(Negate(r), order)),
                        moment(order))))));
        Formula transportError = Call("norm", Subtract(
            complexBudget(b),
            Multiply(Call("ofReal", Divide(a, b)), finiteTransport)));
        Formula tail = Multiply(
            Divide(Multiply(D(2), a), b),
            budget(a),
            Divide(
                Power(Call("abs", r), Add(m, D(1))),
                Subtract(D(1), Call("abs", r))));
        Formula assumptions = All(
            Equal(Call("map", Lambda(xi, real, Negate(xi)), nu), nu),
            Less(D(0), a),
            Less(D(0), b),
            Call("Integrable", Lambda(xi, real, budgetIntegrand(a)), nu));

        return F.Disp(ForAll(
            [
                Bound("nu", measure),
                Bound("a", real),
                Bound("b", real),
                Bound("M", natural),
            ],
            Implies(assumptions,
                new Formula.Relation(
                    transportError,
                    FormulaRelationOperator.LessThanOrEqual,
                    tail))));
    }

}
