using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class ObserverZeroDistanceFibersDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ContinuousObservables/ObserverZeroDistanceFibers."
            + "observer_zero_distance_fibers";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit-ball spanning identifies observer fibers with zero-distance classes.",
        H("Observer Zero-Distance Fibers"),
        Blocks(Describe.Lean(
            DescribeId.Create("observer-fibers-are-zero-distance-classes"),
            DeclarationHandle.Create(Declaration),
            H("Readout fibers are exactly the zero-distance classes"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The frozen unit-ball spanning criterion supplies the zero-distance "
                    + "equivalence. Set extensionality gives the fiber identity; point "
                    + "separation and a hidden-kernel pair give the two endpoint consequences."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type"), state = F.Id("X"), observable = F.Id("A");
        Formula cost = F.Id("L"), rho = F.Id("rho"), sigma = F.Id("sigma"), f = F.Id("f");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula extended = Seq(OpenBracket, D(0), Comma, Sp, Infty, CloseBracket);
        Formula observableType = Call("Submodule", real, Call("ellInfty", state, real));
        Formula same = BindMany([Bound("f", observable)],
            Equal(Apply(f, rho), Apply(f, sigma)));
        Formula distanceZero = Equal(Call("observerDistance", observable, cost, rho, sigma), D(0));
        Formula zeroCriterion = BindMany([Bound("rho", state), Bound("sigma", state)],
            Iff(distanceZero, same));
        Formula readoutFiber = new Formula.SetBuilder(same, sigma, state);
        Formula zeroFiber = new Formula.SetBuilder(distanceZero, sigma, state);
        Formula fiberIdentity = BindMany([Bound("rho", state)], Equal(readoutFiber, zeroFiber));
        Formula separates = BindMany([Bound("rho", state), Bound("sigma", state)],
            Implies(same, Equal(rho, sigma)));
        Formula metricSeparation = Implies(separates,
            BindMany([Bound("rho", state), Bound("sigma", state)],
                Implies(distanceZero, Equal(rho, sigma))));
        Formula distinct = new Formula.Relation(rho, FormulaRelationOperator.NotEqual, sigma);
        Formula hiddenPair = ExistsMany([Bound("rho", state), Bound("sigma", state)],
            And(distinct, same));
        Formula zeroPair = ExistsMany([Bound("rho", state), Bound("sigma", state)],
            And(distinct, distanceZero));
        Formula hiddenConsequence = Implies(hiddenPair, zeroPair);
        Formula homogeneous = BindMany([Bound("c", real), Bound("f", observable)],
            Equal(Apply(cost, Call("smul", F.Id("c"), f)),
                Multiply(new Formula.Absolute(F.Id("c")), Apply(cost, f))));
        Formula spanPremise = Equal(Call("span", real, Call("unitBall", observable, cost)), observable);
        Formula conclusion = And(zeroCriterion,
            And(fiberIdentity, And(metricSeparation, hiddenConsequence)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("X", type), Bound("A", observableType), Bound("L", Arrow(observable, extended))],
            Implies(And(homogeneous, spanPremise), conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula BindMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula ExistsMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
