using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class ResolventFrontierGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Budget/ResolventFrontierGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convex mixing of positive spectral completions controls both the white-floor "
            + "frontier and its minimal resolvent cost.",
        H("Resolvent Frontier Geometry"),
        Blocks(Describe.Lean(
            DescribeId.Create("resolvent-frontier-basic-properties"),
            DeclarationHandle.Create(Prefix + "resolvent_frontier_basic_properties"),
            H("Basic properties of the budget frontier"),
            StatementSource.FromAuthor(FrontierFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Nested conditional-supremum bounds prove concavity without an optimizer. "
                    + "The dual conditional-infimum argument proves convexity of minimal "
                    + "cost, while local-reading nesting gives window antitonicity."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula value) =>
        Call("apply", function, value);

    private static Formula ApplyTwo(Formula function, Formula first, Formula second) =>
        Call("applyTwo", function, first, second);

    private static Formula ApplyFour(
        Formula function, Formula first, Formula second, Formula third, Formula fourth) =>
        Call("applyFour", function, first, second, third, fourth);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Seq(F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body);

    private static Formula Let(string name, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, F.Id(name), Sp, Eq, Sp, value, Comma, Sp);

    private static Formula FrontierFormula()
    {
        Formula prop = F.Id("Prop"), real = Call("Real");
        Formula measure = Call("Measure", real);
        Formula a = F.Id("a"), localMatches = F.Id("localMatches");
        Formula budget = F.Id("resolventBudget"), whiteFloor = F.Id("whiteFloor");
        Formula fullFloor = F.Id("fullFloor"), mix = F.Id("mix");
        Formula l = F.Id("L"), lOne = F.Id("L1"), lTwo = F.Id("L2");
        Formula c = F.Id("C"), cOne = F.Id("C1"), cTwo = F.Id("C2");
        Formula lambda = F.Id("lambda"), r = F.Id("r"), costValue = F.Id("c");
        Formula nu = F.Id("nu"), nuOne = F.Id("nu1"), nuTwo = F.Id("nu2");
        Formula p = F.Id("p"), q = F.Id("q");
        Formula frontierValues = F.Id("frontierValues");
        Formula costValues = F.Id("costValues");
        Formula feasibleBudgets = F.Id("feasibleBudgets");
        Formula feasibleFloors = F.Id("feasibleFloors");
        Formula frontier = F.Id("frontier"), minimalCost = F.Id("minimalCost");

        Formula Match(Formula window, Formula completion) =>
            ApplyTwo(localMatches, window, completion);
        Formula Budget(Formula completion) => Apply(budget, completion);
        Formula Floor(Formula completion) => Apply(whiteFloor, completion);
        Formula Mix(Formula weightOne, Formula weightTwo,
                Formula completionOne, Formula completionTwo) =>
            ApplyFour(mix, weightOne, weightTwo, completionOne, completionTwo);
        Formula Combo(Formula weightOne, Formula valueOne,
                Formula weightTwo, Formula valueTwo) =>
            Call("add", Call("mul", weightOne, valueOne),
                Call("mul", weightTwo, valueTwo));

        Formula denominator = Call("mul", D(2), a);
        Formula assumptions = All(
            Greater(a, D(0)),
            ForAll([Bound("nu", measure)], AtMost(D(0), Budget(nu))),
            ForAll([Bound("nu", measure)], AtMost(D(0), Floor(nu))),
            ForAll(
                [Bound("L", real), Bound("nu", measure)],
                Implies(Match(l, nu), AtMost(Floor(nu), Apply(fullFloor, l)))),
            ForAll(
                [Bound("nu", measure)],
                AtMost(Call("div", Floor(nu), denominator), Budget(nu))),
            ForAll(
                [Bound("L1", real), Bound("L2", real), Bound("nu", measure)],
                Implies(
                    AtMost(lOne, lTwo),
                    Implies(Match(lTwo, nu), Match(lOne, nu)))),
            ForAll(
                [
                    Bound("p", real), Bound("q", real), Bound("L", real),
                    Bound("nu1", measure), Bound("nu2", measure),
                ],
                Implies(
                    All(AtMost(D(0), p), AtMost(D(0), q),
                        Equal(Call("add", p, q), D(1)),
                        Match(l, nuOne), Match(l, nuTwo)),
                    Match(l, Mix(p, q, nuOne, nuTwo)))),
            ForAll(
                [
                    Bound("p", real), Bound("q", real),
                    Bound("nu1", measure), Bound("nu2", measure),
                ],
                Equal(
                    Budget(Mix(p, q, nuOne, nuTwo)),
                    Combo(p, Budget(nuOne), q, Budget(nuTwo)))),
            ForAll(
                [
                    Bound("p", real), Bound("q", real),
                    Bound("nu1", measure), Bound("nu2", measure),
                ],
                Implies(
                    All(AtMost(D(0), p), AtMost(D(0), q),
                        Equal(Call("add", p, q), D(1))),
                    AtMost(
                        Combo(p, Floor(nuOne), q, Floor(nuTwo)),
                        Floor(Mix(p, q, nuOne, nuTwo))))));

        Formula frontierSet = new Formula.SetBuilder(
            Exists(
                [Bound("nu", measure)],
                All(Match(l, nu), AtMost(Budget(nu), c), Equal(r, Floor(nu)))),
            r,
            real);
        Formula costSet = new Formula.SetBuilder(
            Exists(
                [Bound("nu", measure)],
                All(Match(l, nu), AtMost(lambda, Floor(nu)),
                    Equal(costValue, Budget(nu)))),
            costValue,
            real);
        Formula frontierAt(Formula window, Formula cap) =>
            ApplyTwo(frontier, window, cap);
        Formula frontierValuesAt(Formula window, Formula cap) =>
            ApplyTwo(frontierValues, window, cap);
        Formula costValuesAt(Formula window, Formula floorLevel) =>
            ApplyTwo(costValues, window, floorLevel);

        Formula definitions = Seq(
            Let("frontierValues", Lambda("L", real, Lambda("C", real, frontierSet))),
            Let("costValues", Lambda("L", real, Lambda("lambda", real, costSet))),
            Let("feasibleBudgets", Lambda(
                "L", real, new Formula.SetBuilder(
                    Call("Nonempty", frontierValuesAt(l, c)), c, real))),
            Let("feasibleFloors", Lambda(
                "L", real, new Formula.SetBuilder(
                    Call("Nonempty", costValuesAt(l, lambda)), lambda, real))),
            Let("frontier", Lambda(
                "L", real, Lambda("C", real, Call("sSup", frontierValuesAt(l, c))))),
            Let("minimalCost", Lambda(
                "L", real, Lambda(
                    "lambda", real, Call("sInf", costValuesAt(l, lambda))))),
            All(
                ForAll(
                    [Bound("L", real), Bound("C", real)],
                    Implies(
                        Member(c, Apply(feasibleBudgets, l)),
                        All(
                            AtMost(D(0), frontierAt(l, c)),
                            AtMost(
                                frontierAt(l, c),
                                Call("min", Apply(fullFloor, l),
                                    Call("mul", denominator, c)))))),
                ForAll(
                    [Bound("L", real)],
                    Call("MonotoneOn", Apply(frontier, l), Apply(feasibleBudgets, l))),
                ForAll(
                    [Bound("L", real)],
                    Call("ConcaveOn", real, Apply(feasibleBudgets, l), Apply(frontier, l))),
                ForAll(
                    [Bound("C", real)],
                    Call(
                        "AntitoneOn",
                        Seq(Open, Lambda("L", real, frontierAt(l, c)), Close),
                        new Formula.SetBuilder(
                            Call("Nonempty", frontierValuesAt(l, c)), l, real))),
                ForAll(
                    [Bound("L", real)],
                    Call("MonotoneOn", Apply(minimalCost, l), Apply(feasibleFloors, l))),
                ForAll(
                    [Bound("L", real)],
                    Call("ConvexOn", real, Apply(feasibleFloors, l),
                        Apply(minimalCost, l)))));

        return F.Disp(ForAll(
            [
                Bound("a", real),
                Bound("localMatches", new Formula.TypeArrow(
                    real, new Formula.TypeArrow(measure, prop))),
                Bound("resolventBudget", new Formula.TypeArrow(measure, real)),
                Bound("whiteFloor", new Formula.TypeArrow(measure, real)),
                Bound("fullFloor", new Formula.TypeArrow(real, real)),
                Bound("mix", new Formula.TypeArrow(
                    real, new Formula.TypeArrow(
                        real, new Formula.TypeArrow(
                            measure, new Formula.TypeArrow(measure, measure))))),
            ],
            Implies(assumptions, definitions)));
    }
}
