using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class LiCurvatureCriterionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/TestFunctions/LiCurvatureCriterion.li_curvature_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Toeplitz positivity of every Li-curvature section is equivalent to the "
            + "Riemann hypothesis under the stated representation interfaces.",
        H("Li Curvature Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("li-curvature-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Li curvature criterion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The statement keeps the Li criterion, the canonical initial data "
                        + "and curvature recurrence, and the two common probability-"
                        + "measure representations as explicit interfaces. These are the "
                        + "ingredients not supplied together by the pinned library.")),
                Paragraph(Text(
                    "For the forward direction, the circle-moment representation turns "
                        + "each Toeplitz quadratic form into the integral of the squared "
                        + "modulus of its analytic coefficient polynomial.")),
                Paragraph(Text(
                    "For the reverse direction, the finite geometric polynomial has empty "
                        + "sum at zero. Its squared modulus reconstructs a nonnegative Li "
                        + "sequence with the prescribed first two values and second "
                        + "differences. Two-step recurrence uniqueness identifies it with "
                        + "the supplied Li sequence, after which the Li criterion applies."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Natural");
        Formula integer = Call("Integer");
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula circle = Call("Circle");
        Formula c = F.Id("c");
        Formula coefficient = F.Id("lambda");
        Formula n = F.Id("n");
        Formula depth = F.Id("N");
        Formula mu = F.Id("mu");
        Formula rh = Call("RiemannHypothesis");
        Formula measureType = Call("Measure", circle);

        Formula Curvature(Formula index) => Add(
            Sub(
                Apply(coefficient, Add(index, D(1))),
                Mul(D(2), Apply(coefficient, index))),
            Apply(coefficient, Sub(index, D(1))));
        Formula Moment(Formula measure, Formula index) =>
            Call("circleMoment", measure, index);
        Formula Toeplitz(Formula size) =>
            Call("toeplitzMatrix", c, size);
        Formula ToeplitzPositive() => ForAll(
            [Bound("N", natural)],
            Call("PosSemidef", Toeplitz(depth)));
        Formula MeasureRepresentation() => Exists(
            [Bound("mu", measureType)],
            All(
                Call("IsProbabilityMeasure", mu),
                ForAll(
                    [Bound("k", integer)],
                    Equal(Apply(c, F.Id("k")), Moment(mu, F.Id("k"))))));

        Formula coefficientNonnegative = ForAll(
            [Bound("n", natural)],
            LessEqual(D(0), Apply(coefficient, n)));
        Formula liCriterion = Iff(rh, coefficientNonnegative);
        Formula zeroValue = Equal(Apply(coefficient, D(0)), D(0));
        Formula oneNonnegative = LessEqual(D(0), Apply(coefficient, D(1)));
        Formula recurrence = ForAll(
            [Bound("n", natural)],
            Implies(
                LessEqual(D(1), n),
                Equal(
                    Curvature(n),
                    Mul(
                        Mul(D(2), Apply(coefficient, D(1))),
                        Call("realPart", Apply(c, n))))));
        Formula rhRepresentation = Implies(rh, MeasureRepresentation());
        Formula herglotzRepresentation = Implies(
            ToeplitzPositive(),
            MeasureRepresentation());
        Formula assumptions = All(
            liCriterion,
            zeroValue,
            oneNonnegative,
            recurrence,
            rhRepresentation,
            herglotzRepresentation);

        return Disp(ForAll(
            [
                Bound("c", Arrow(integer, complex)),
                Bound("lambda", Arrow(natural, real)),
            ],
            Implies(assumptions, Iff(rh, ToeplitzPositive()))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
