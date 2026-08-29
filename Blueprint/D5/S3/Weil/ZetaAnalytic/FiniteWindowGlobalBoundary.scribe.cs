using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaAnalytic;

internal sealed class FiniteWindowGlobalBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaAnalytic/FiniteWindowGlobalBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-window sampling floors are positive, while gap approximants force the "
            + "global floor to vanish.",
        H("Finite Window and Global Boundary"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-window-positive-global-boundary"),
            DeclarationHandle.Create(Prefix + "finite_window_positive_global_boundary"),
            H("Finite windows are interior and the global limit is boundary"),
            StatementSource.FromAuthor(BoundaryFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Conditional completeness turns each positive frame witness into a "
                    + "strictly positive unit-sphere infimum. Nested admissibility carries "
                    + "each vanishing-energy gap probe into all larger windows, which gives "
                    + "the upper half of the order-topology limit."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula value) =>
        Call("apply", function, value);

    private static Formula ApplyTwo(Formula function, Formula first, Formula second) =>
        Call("applyTwo", function, first, second);

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

    private static Formula Square(Formula value) => new Formula.Power(Seq(value), D(2));

    private static Formula Norm(Formula value) => new Formula.Norm(value);

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

    private static Formula BoundaryFormula()
    {
        Formula type = F.Id("Type"), prop = F.Id("Prop");
        Formula real = Call("Real"), natural = Call("Nat");
        Formula source = F.Id("H"), target = F.Id("K");
        Formula sampling = F.Id("sampling"), window = F.Id("windowAdmissible");
        Formula probe = F.Id("probe"), probeWindow = F.Id("probeWindow");
        Formula floor = F.Id("floor"), l = F.Id("L"), lOne = F.Id("L1");
        Formula lTwo = F.Id("L2"), f = F.Id("f"), c = F.Id("c");
        Formula n = F.Id("n"), r = F.Id("r");

        Formula sampleEnergy = Square(Norm(Apply(sampling, f)));
        Formula probeAt = Apply(probe, n);
        Formula probeEnergy = Square(Norm(Apply(sampling, probeAt)));
        Formula nestedWindows = ForAll(
            [Bound("L1", real), Bound("L2", real)],
            Implies(
                AtMost(lOne, lTwo),
                ForAll(
                    [Bound("f", source)],
                    Implies(
                        ApplyTwo(window, lOne, f),
                        ApplyTwo(window, lTwo, f)))));
        Formula unitWindows = ForAll(
            [Bound("L", real)],
            Implies(
                Greater(l, D(0)),
                Exists(
                    [Bound("f", source)],
                    And(ApplyTwo(window, l, f), Equal(Norm(f), D(1))))));
        Formula finiteFrameBounds = ForAll(
            [Bound("L", real)],
            Implies(
                Greater(l, D(0)),
                Exists(
                    [Bound("c", real)],
                    And(
                        Greater(c, D(0)),
                        ForAll(
                            [Bound("f", source)],
                            Implies(
                                ApplyTwo(window, l, f),
                                AtMost(
                                    Call("mul", c, Square(Norm(f))),
                                    sampleEnergy)))))));
        Formula probeUnit = ForAll(
            [Bound("n", natural)], Equal(Norm(probeAt), D(1)));
        Formula probesAdmissible = ForAll(
            [Bound("n", natural)],
            ApplyTwo(window, Apply(probeWindow, n), probeAt));
        Formula probesVanish = Call(
            "Tendsto",
            Seq(Open, Lambda("n", natural, probeEnergy), Close),
            F.Id("atTop"),
            Call("nhds", D(0)));

        Formula floorValues = new Formula.SetBuilder(
            Exists(
                [Bound("f", source)],
                All(
                    ApplyTwo(window, l, f),
                    Equal(Norm(f), D(1)),
                    Equal(r, sampleEnergy))),
            r,
            real);
        Formula floorBody = Call("sInf", floorValues);
        Formula localPositive = ForAll(
            [Bound("L", real)],
            Implies(Greater(l, D(0)), Greater(Apply(floor, l), D(0))));
        Formula globalLimit = Call(
            "Tendsto", floor, F.Id("atTop"), Call("nhds", D(0)));
        Formula conclusion = Seq(
            Operatorname, Grp(F.Id("let")), Sp, floor, Sp, Eq, Sp,
            Lambda("L", real, floorBody), Comma, Sp,
            And(localPositive, globalLimit));

        Formula assumptions = All(
            Call("NormedAddCommGroup", source),
            Call("NormedSpace", real, source),
            Call("NormedAddCommGroup", target),
            Call("NormedSpace", real, target),
            nestedWindows,
            unitWindows,
            finiteFrameBounds,
            probeUnit,
            probesAdmissible,
            probesVanish);

        return F.Disp(ForAll(
            [
                Bound("H", type),
                Bound("K", type),
                Bound("sampling", Call("ContinuousLinearMap", real, source, target)),
                Bound("windowAdmissible", new Formula.TypeArrow(
                    real, new Formula.TypeArrow(source, prop))),
                Bound("probe", new Formula.TypeArrow(natural, source)),
                Bound("probeWindow", new Formula.TypeArrow(natural, real)),
            ],
            Implies(assumptions, conclusion)));
    }
}
