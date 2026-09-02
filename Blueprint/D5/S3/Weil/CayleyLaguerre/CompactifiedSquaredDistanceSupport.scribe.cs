using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class CompactifiedSquaredDistanceSupportDocument
    : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/CayleyLaguerre/CompactifiedSquaredDistanceSupport."
            + "compactified_squared_distance_support_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational compactification separates nonnegative and negative squared "
            + "distances and characterizes critical-line support.",
        H("Compactified Squared-Distance Support"),
        Blocks(Describe.Lean(
            DescribeId.Create("compactified-squared-distance-support-criterion"),
            DeclarationHandle.Create(Handle),
            H("Compactified squared-distance support criterion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The compact coordinate is the source rational map, constructed "
                        + "from the supplied scale. Nonnegative inputs land in the unit "
                        + "interval, while a genuine signed squared distance in the "
                        + "critical strip lands strictly below negative one.")),
                Paragraph(Text(
                    "For every Mathlib-nontrivial zeta zero, the observed signed squared "
                        + "distance is constructed from its real coordinate. Requiring "
                        + "the rational coordinate to be defined and supported in the "
                        + "closed unit interval is equivalent to the stated critical-line "
                        + "hypothesis."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Nat");
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula a = F.Id("a");
        Formula x = F.Id("x");
        Formula delta = F.Id("delta");
        Formula rho = F.Id("rho");
        Formula n = F.Id("n");
        Formula y = F.Id("y");
        Formula compactCoordinate = F.Id("compactCoordinate");
        Formula signedSquaredDistance = F.Id("signedSquaredDistance");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula quarter = new Formula.Fraction(D(1), D(4));
        Formula deltaSquared = new Formula.Power(delta, D(2));
        Formula negativeDeltaSquared = Seq(Minus, deltaSquared);

        Formula compactDefinition = Lambda(
            y,
            new Formula.Fraction(Subtract(y, a), Add(y, a)));
        Formula sourcePremises = And(
            Less(quarter, a),
            And(
                AtMost(D(0), x),
                And(
                    Less(D(0), Call("abs", delta)),
                    Less(deltaSquared, quarter))));

        Formula nonnegativeClause = And(
            AtMost(new Formula.Negate(D(1)), Apply(compactCoordinate, x)),
            Less(Apply(compactCoordinate, x), D(1)));
        Formula offLineCoordinate = Apply(
            compactCoordinate,
            negativeDeltaSquared);
        Formula offLineValue = Seq(Minus, new Formula.Fraction(
            Add(a, deltaSquared),
            Subtract(a, deltaSquared)));
        Formula offLineClause = And(
            Equal(offLineCoordinate, offLineValue),
            Less(offLineCoordinate, new Formula.Negate(D(1))));

        Formula trivialZeroValue = Seq(
            Minus,
            Multiply(D(2), Add(n, D(1))));
        Formula trivialZero = Exists(
            [Bound("n", natural)],
            Equal(rho, trivialZeroValue));
        Formula zeroPremises = And(
            Equal(Call("riemannZeta", rho), D(0)),
            And(
                new Formula.Not(trivialZero),
                NotEqual(rho, D(1))));
        Formula signedDistanceValue = Seq(
            Minus,
            new Formula.Power(Subtract(Call("re", rho), half), D(2)));
        Formula supportClause = And(
            NotEqual(Add(signedSquaredDistance, a), D(0)),
            Member(
                Apply(compactCoordinate, signedSquaredDistance),
                Call("Icc", new Formula.Negate(D(1)), D(1))));
        Formula allZerosSupported = ForAll(
            [Bound("rho", complex)],
            Implies(
                zeroPremises,
                Seq(
                    Let("signedSquaredDistance", signedDistanceValue),
                    supportClause)));
        Formula criticalSupportCriterion = Iff(
            Call("RiemannHypothesis"),
            allZerosSupported);
        Formula conclusion = And(
            nonnegativeClause,
            And(offLineClause, criticalSupportCriterion));

        return Disp(ForAll(
            [
                Bound("a", real),
                Bound("x", real),
                Bound("delta", real),
            ],
            Implies(
                sourcePremises,
                Seq(
                    Let("compactCoordinate", compactDefinition),
                    conclusion))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Let(string name, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, F.Id(name), Sp, Eq, Sp, value, Comma, Sp);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
