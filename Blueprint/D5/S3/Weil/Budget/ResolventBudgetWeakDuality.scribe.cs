using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class ResolventBudgetWeakDualityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Budget/ResolventBudgetWeakDuality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local matching and resolvent feasibility give weak primal-dual order.",
        H("Resolvent Budget Weak Duality"),
        Blocks(Describe.Lean(
            DescribeId.Create("resolvent-budget-weak-duality"),
            DeclarationHandle.Create(Prefix + "resolvent_budget_weak_duality"),
            H("Feasible primal floors lie below feasible dual values"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public carrier is a positive real-line measure. Fourier reading, "
                        + "evaluation at zero, and local source pairing are supplied on one "
                        + "test carrier; the pairing identity states their local match.")),
                Paragraph(Text(
                    "Integrability makes both signed integrals honest. Pointwise Fourier "
                        + "majorization integrates against the positive measure, while "
                        + "nonnegative dual pressure scales the primal budget inequality.")),
                Paragraph(Text(
                    "The floor constraint then combines the two estimates into the displayed "
                        + "weak-duality bound."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula test = F.Id("Test");
        Formula fourier = F.Id("fourierReading");
        Formula atZero = F.Id("atZero");
        Formula pairing = F.Id("weilPairing");
        Formula measure = F.Id("mu");
        Formula phi = F.Id("phi");
        Formula xi = F.Id("xi");
        Formula a = F.Id("a");
        Formula lambda = F.Id("lambda");
        Formula theta = F.Id("theta");
        Formula budget = F.Id("C");
        Formula realMeasure = Call("Measure", real);
        Formula weight = new Formula.Fraction(
            D(1),
            Seq(new Formula.Power(xi, D(2)), Sp, Plus, Sp,
                new Formula.Power(a, D(2))));
        Formula fourierAtPhi = Apply(fourier, phi);
        Formula fourierAtXi = Apply(fourierAtPhi, xi);
        Formula integralFourier = Call(
            "integral", measure, Lambda(xi, real, fourierAtXi));
        Formula integralWeight = Call(
            "integral", measure, Lambda(xi, real, weight));
        Formula denominator = Seq(D(2), Sp, Cdot, Sp, a);

        Formula assumptions = All(
            AtMost(D(0), lambda),
            AtMost(D(0), theta),
            Call("Integrable", Lambda(xi, real, fourierAtXi), measure),
            Call("Integrable", Lambda(xi, real, weight), measure),
            Equal(
                Apply(pairing, phi),
                Seq(lambda, Sp, Cdot, Sp, Apply(atZero, phi), Sp, Plus, Sp,
                    integralFourier)),
            ForAll(
                [Bound("xi", real)],
                AtMost(
                    D(0),
                    Seq(fourierAtXi, Sp, Plus, Sp,
                        theta, Sp, Cdot, Sp, weight))),
            AtMost(
                D(1),
                Seq(Apply(atZero, phi), Sp, Plus, Sp,
                    new Formula.Fraction(theta, denominator))),
            AtMost(
                Seq(new Formula.Fraction(lambda, denominator), Sp, Plus, Sp,
                    integralWeight),
                budget));
        Formula conclusion = AtMost(
            lambda,
            Seq(Apply(pairing, phi), Sp, Plus, Sp,
                theta, Sp, Cdot, Sp, budget));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(test, type), Comma, Sp,
                Typed(fourier, Arrow(test, Arrow(real, real))), Comma),
            Seq(
                Typed(atZero, Arrow(test, real)), Comma, Sp,
                Typed(pairing, Arrow(test, real)), Comma),
            Seq(
                Typed(measure, realMeasure), Comma, Sp,
                Typed(phi, test), Comma, Sp,
                Typed(a, real), Comma, Sp,
                Typed(lambda, real), Comma, Sp,
                Typed(theta, real), Comma, Sp,
                Typed(budget, real), Comma),
            Seq(assumptions, Sp, Rightarrow),
            Seq(conclusion, Dot),
        ]));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula Typed(Formula value, Formula domain) =>
        Seq(value, Colon, Sp, domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Lambda(Formula name, Formula domain, Formula body) =>
        Seq(name, Colon, Sp, domain, Sp, Mapsto, Sp, body);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
