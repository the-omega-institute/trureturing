using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class AnchoredObserverDistanceInvarianceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ContinuousObservables/AnchoredObserverDistanceInvariance."
            + "anchored_observer_distance_invariance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible group actions preserve observer distance and anchored radius.",
        H("Anchored Observer Distance Invariance"),
        Blocks(Describe.Lean(
            DescribeId.Create("compatible-actions-preserve-anchored-observer-distance"),
            DeclarationHandle.Create(Declaration),
            H("Compatible actions preserve the observer geometry"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The action transports every admissible observable, preserves its cost, "
                    + "and commutes with evaluation. Reindexing the unit-cost supremum by "
                    + "the inverse action proves distance invariance in both directions."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type"), group = F.Id("G"), observable = F.Id("A");
        Formula state = F.Id("X"), family = F.Id("O"), cost = F.Id("L");
        Formula evaluate = F.Id("e"), origin = F.Id("o"), g = F.Id("g");
        Formula f = F.Id("f"), x = F.Id("x"), y = F.Id("y");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula extended = Seq(OpenBracket, D(0), Comma, Sp, Infty, CloseBracket);
        Formula actionGF = Call("act", g, f), actionGX = Call("act", g, x);
        Formula actionGY = Call("act", g, y), actionGO = Call("act", g, origin);
        Formula distanceOO = Call("observerDistance", family, cost, evaluate, origin, origin);
        Formula distanceXY = Call("observerDistance", family, cost, evaluate, x, y);
        Formula distanceGXY = Call("observerDistance", family, cost, evaluate, actionGX, actionGY);
        Formula distanceOGX = Call("observerDistance", family, cost, evaluate, origin, actionGX);
        Formula distanceOX = Call("observerDistance", family, cost, evaluate, origin, x);

        Formula instances = And(Call("Group", group),
            And(Call("MulAction", group, observable), Call("MulAction", group, state)));
        Formula closed = BindMany([Bound("g", group), Bound("f", observable)],
            Implies(Member(f, family), Member(actionGF, family)));
        Formula costInvariant = BindMany([Bound("g", group), Bound("f", observable)],
            Implies(Member(f, family), Equal(Apply(cost, actionGF), Apply(cost, f))));
        Formula compatible = BindMany(
            [Bound("g", group), Bound("f", observable), Bound("x", state)],
            Equal(Apply(evaluate, actionGX, actionGF), Apply(evaluate, x, f)));
        Formula distanceInvariant = BindMany(
            [Bound("g", group), Bound("x", state), Bound("y", state)],
            Equal(distanceGXY, distanceXY));
        Formula anchored = BindMany([Bound("g", group), Bound("x", state)],
            Implies(Equal(actionGO, origin), Equal(distanceOGX, distanceOX)));
        Formula conclusion = And(Equal(distanceOO, D(0)), And(distanceInvariant, anchored));
        Formula assumptions = And(instances, And(closed, And(costInvariant, compatible)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("G", type), Bound("A", type), Bound("X", type),
                Bound("O", Call("Set", observable)),
                Bound("L", Arrow(observable, extended)),
                Bound("e", Arrow(state, Arrow(observable, real))), Bound("o", state)],
            Implies(assumptions, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula BindMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
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
