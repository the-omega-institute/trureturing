using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class FiniteAtomicBudgetedCompletionDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/TestFunctions/FiniteAtomicBudgetedCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An active complementary gap forces an even optimizer to be finite atomic.",
        H("Finite Atomic Budgeted Completion"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-atomic-budgeted-completion"),
            DeclarationHandle.Create(Handle + "finite_atomic_budgeted_completion"),
            H("Active budget gives a finite symmetric atomic completion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Complementary contact support places the residual measure on the real "
                        + "zeros of the canonical entire contact function. Positive pressure "
                        + "and Schwartz decay confine those zeros to a compact interval.")),
                Paragraph(Text(
                    "Analytic isolation makes the real contact set finite. Evenness then "
                        + "splits every singleton mass equally between its positive and "
                        + "negative Dirac representatives, including the possible zero atom."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula nonnegativeReal = Call("NNReal");
        Formula extendedNonnegativeReal = Call("ENNReal");
        Formula test = Call("WeilTestFunction");
        Formula a = F.Id("a"), theta = F.Id("theta"), lambda = F.Id("lambda");
        Formula phi = F.Id("phi"), residual = F.Id("residual");
        Formula completion = F.Id("completion"), x = F.Id("x"), xi = F.Id("xi");
        Formula indexType = F.Id("I"), point = F.Id("point");
        Formula weight = F.Id("weight"), weightZero = F.Id("weightZero");
        Formula r = F.Id("r");

        Formula Transform(Formula value) => Call("fourierLaplace", phi, value);
        Formula Square(Formula value) =>
            new Formula.Power(Seq(Open, value, Close), D(2));
        Formula Denominator(Formula value) => Add(Square(value), Square(a));
        Formula Gap(Formula value) =>
            Add(Call("realPart", Transform(value)), Div(theta, Denominator(value)));
        Formula EntireContact(Formula value) =>
            Add(Mul(Denominator(value), Transform(value)), theta);
        Formula PointAt(Formula index) => Apply(point, index);
        Formula WeightAt(Formula index) => Apply(weight, index);
        Formula Negate(Formula value) => new Formula.Negate(value);
        Formula Lambda(Formula variable, Formula domain, Formula body) =>
            Seq(Open, variable, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

        Formula whiteCoefficient = Call(
            "ofReal",
            Div(
                Call("toReal", lambda),
                Mul(D(2), Call("pi"))));
        Formula whiteMeasure = Call(
            "smul",
            whiteCoefficient,
            Call("volume", real));
        Formula atomicResidual = Call(
            "sum",
            r,
            indexType,
            Call(
                "smul",
                WeightAt(r),
                Add(
                    Call("dirac", PointAt(r)),
                    Call("dirac", Negate(PointAt(r))))));
        Formula zeroAtom = Call("smul", weightZero, Call("dirac", D(0)));

        Formula realTest = ForAll(
            [Bound("x", real)],
            Equal(Call("conj", Apply(phi, x)), Apply(phi, x)));
        Formula contactNonnegative = ForAll(
            [Bound("xi", real)],
            LessEqual(D(0), Gap(xi)));
        Formula contactIntegrable = Call(
            "Integrable",
            Lambda(xi, real, Gap(xi)),
            residual);
        Formula residualBudgetIntegrable = Call(
            "Integrable",
            Lambda(xi, real, Div(D(1), Denominator(xi))),
            residual);
        Formula complementarity = Equal(
            Call("integral", xi, real, Gap(xi), residual),
            D(0));
        Formula residualEven = Equal(
            Call("map", Lambda(xi, real, Negate(xi)), residual),
            residual);
        Formula completionSplit = Equal(
            completion,
            Add(whiteMeasure, residual));
        Formula assumptions = All(
            Less(D(0), a),
            Less(D(0), theta),
            realTest,
            contactNonnegative,
            contactIntegrable,
            residualBudgetIntegrable,
            complementarity,
            residualEven,
            completionSplit);

        Formula contactZeros = ForAll(
            [Bound("r", indexType)],
            All(
                Equal(EntireContact(PointAt(r)), D(0)),
                Equal(EntireContact(Negate(PointAt(r))), D(0))));
        Formula finiteWeights = ForAll(
            [Bound("r", indexType)],
            NotEqual(WeightAt(r), Call("infinity")));
        Formula finiteZeroWeight = NotEqual(weightZero, Call("infinity"));
        Formula finiteAtomicCompletion = Equal(
            completion,
            Add(Add(whiteMeasure, atomicResidual), zeroAtom));
        Formula conclusion = Exists(
            [
                Bound("I", type),
                Bound("finiteI", Call("Fintype", indexType)),
                Bound("point", new Formula.TypeArrow(indexType, real)),
                Bound("weight", new Formula.TypeArrow(indexType, extendedNonnegativeReal)),
                Bound("weightZero", extendedNonnegativeReal),
            ],
            All(finiteWeights, finiteZeroWeight, contactZeros, finiteAtomicCompletion));

        return Disp(ForAll(
            [
                Bound("a", real),
                Bound("theta", real),
                Bound("lambda", nonnegativeReal),
                Bound("phi", test),
                Bound("residual", Call("Measure", real)),
                Bound("completion", Call("Measure", real)),
            ],
            Implies(assumptions, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

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

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
