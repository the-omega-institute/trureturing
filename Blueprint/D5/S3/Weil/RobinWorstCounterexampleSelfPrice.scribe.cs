using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class RobinWorstCounterexampleSelfPriceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A negative Robin-margin minimizer on an admissible set is optimal at its own logarithmic price.",
        H("Robin Worst Counterexample Self-Price"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("robin-worst-counterexample-self-price"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/RobinWorstCounterexampleSelfPrice.robin_worst_counterexample_self_price"),
                H("A worst strict counterexample is self-priced optimal"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The vanishing lower limit of the logarithmic Robin margin makes every "
                            + "sublevel below a strict negative value finite. A minimum on the "
                            + "admissible set therefore exists and remains strictly negative.")),
                    Paragraph(Text(
                        "For the minimizing integer, the derivative of log(log E) at E = log n "
                            + "is 1 divided by E log E. Strict concavity gives the supporting "
                            + "tangent inequality, and the margin identity converts it into the "
                            + "global maximum of the resource objective W minus lambda E."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("A"), n = F.Id("n"), star = F.Id("nstar");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula margin = F.Id("robinLogMargin");
        Formula objective = F.Id("goldenResourceObjective");
        Formula energy = Log(star);
        Formula price = new Formula.Fraction(Num(1), Product(energy, Log(energy)));
        Formula admissible = ForAll([Bound("n", nat)],
            Implies(In(n, a), Le(Num(5041), n)));
        Formula counterexample = Exists([Bound("n", nat)],
            And(In(n, a), Lt(Call(margin, n), Num(0))));
        Formula minimum = ForAll([Bound("n", nat)],
            Implies(In(n, a), Le(Call(margin, star), Call(margin, n))));
        Formula selfPrice = ForAll([Bound("n", nat)],
            Implies(In(n, a), Le(Call(objective, price, n), Call(objective, price, star))));
        Formula conclusion = Exists([Bound("nstar", nat)],
            And(In(star, a), And(Lt(Call(margin, star), Num(0)),
                And(minimum, selfPrice))));
        return Disp(ForAll([Bound("A", Call("Set", nat))],
            Implies(And(admissible, counterexample), conclusion)));
    }

    private static Formula Log(Formula value) => Call("log", value);

    private static Formula In(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
