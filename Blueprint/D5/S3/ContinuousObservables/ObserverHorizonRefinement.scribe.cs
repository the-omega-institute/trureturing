using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class ObserverHorizonRefinementDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ContinuousObservables/ObserverHorizonRefinement."
            + "observer_horizon_mono_of_refinement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refinement can only enlarge the infinite-distance observer horizon.",
        H("Observer Horizon Refinement"),
        Blocks(Describe.Lean(
            DescribeId.Create("observer-horizon-is-monotone-under-refinement"),
            DeclarationHandle.Create(Declaration),
            H("The observer horizon grows under refinement"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Every old unit-cost observable remains available after refinement. The "
                    + "frozen distance monotonicity theorem therefore sends an old top-valued "
                    + "distance to a top-valued refined distance."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type"), observable = F.Id("A"), state = F.Id("X");
        Formula oldFamily = F.Id("Am"), newFamily = F.Id("Am1");
        Formula oldCost = F.Id("Lm"), newCost = F.Id("Lm1");
        Formula evaluate = F.Id("e"), origin = F.Id("o"), f = F.Id("f"), x = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula extended = Seq(OpenBracket, D(0), Comma, Sp, Infty, CloseBracket);
        Formula subset = new Formula.Relation(oldFamily, FormulaRelationOperator.SubsetOf, newFamily);
        Formula restriction = new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("f"), observable,
            Implies(Member(f, oldFamily), Equal(Apply(newCost, f), Apply(oldCost, f))));
        Formula oldHorizon = new Formula.SetBuilder(
            Equal(Call("observerDistance", oldFamily, oldCost, evaluate, origin, x), Infty),
            x, state);
        Formula newHorizon = new Formula.SetBuilder(
            Equal(Call("observerDistance", newFamily, newCost, evaluate, origin, x), Infty),
            x, state);
        Formula conclusion = new Formula.Relation(
            oldHorizon, FormulaRelationOperator.SubsetOf, newHorizon);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("A", type), Bound("X", type),
                Bound("e", Arrow(state, Arrow(observable, real))), Bound("o", state),
                Bound("Am", Call("Set", observable)), Bound("Am1", Call("Set", observable)),
                Bound("Lm", Arrow(observable, extended)),
                Bound("Lm1", Arrow(observable, extended))],
            Implies(And(subset, restriction), conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
