using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class FlatQuadraticObserverBundleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One compatible jet and constant second derivative determine a positive quadratic operator bundle.",
        H("Flat Quadratic Observer Bundle"),
        Blocks(Describe.Lean(
            DescribeId.Create("flat-quadratic-observer-bundle"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/Adelic/FlatQuadraticObserverBundle."
                    + "flat_quadratic_observer_bundle"),
            H("A common self-adjoint operator generates every quadratic fiber"),
            StatementSource.FromAuthor(Disp(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The family A and its named velocity live in one partially ordered "
                        + "C-star algebra. Their two derivative laws encode a constant "
                        + "second derivative equal to twice the identity operator.")),
                Paragraph(Text(
                    "Self-adjointness of the entire family makes the velocity at the base "
                        + "point self-adjoint. The displayed compatible jet then fixes the "
                        + "integration constants and constructs the single operator H.")),
                Paragraph(Text(
                    "The resulting affine square agrees with A at every real parameter. "
                        + "Because its affine factor is self-adjoint, every displayed square "
                        + "is positive. The closing determinant and Stieltjes paragraph in "
                        + "the source is an interpretation question outside the named theorem."))),
            DescribeRole.Theorem))));

    private static Formula Apply(string function, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(function), [.. arguments]);

    private static Formula Evaluate(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula type = Apply("Type");
        Formula real = Apply("Real");
        Formula algebra = F.Id("B");
        Formula family = F.Id("A");
        Formula velocity = F.Id("velocity");
        Formula basePoint = F.Id("t0");
        Formula point = F.Id("t");
        Formula familyType = Arrow(real, algebra);
        Formula identity = Apply("one", algebra);
        Formula velocityAtBase = Evaluate(velocity, basePoint);
        Formula halfVelocity = Apply("smul", new Formula.Fraction(D(1), D(2)), velocityAtBase);
        Formula commonOperator = F.Id("H");
        Formula commonOperatorDefinition = Seq(
            Apply("algebraMap", real, algebra, basePoint), Sp, Minus, Sp, halfVelocity);
        Formula affineAtPoint = Seq(
            commonOperator, Sp, Minus, Sp, Apply("algebraMap", real, algebra, point));
        Formula affineSquare = Apply("sq", affineAtPoint);

        Formula firstDerivative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            Apply("HasDerivAt", family, Evaluate(velocity, point), point));
        Formula secondDerivative = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            Apply("HasDerivAt", velocity, Apply("smul", D(2), identity), point));
        Formula selfAdjointFamily = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            Apply("IsSelfAdjoint", Evaluate(family, point)));
        Formula jetIdentity = EqualTo(
            Evaluate(family, basePoint),
            Apply("smul", new Formula.Fraction(D(1), D(4)),
                Apply("sq", velocityAtBase)));
        Formula premises = And(
            Apply("CStarAlgebra", algebra),
            And(
                Apply("PartialOrder", algebra),
                And(
                    Apply("StarOrderedRing", algebra),
                    And(firstDerivative,
                        And(secondDerivative, And(selfAdjointFamily, jetIdentity))))));

        Formula squareIdentity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            EqualTo(Evaluate(family, point), affineSquare));
        Formula positivity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            LessThanOrEqual(D(0), affineSquare));
        Formula conclusions = And(
            Apply("IsSelfAdjoint", commonOperator),
            And(squareIdentity, positivity));
        Formula letConclusion = Seq(
            F.Id("let"), Sp, commonOperator, Colon, Sp, algebra, Sp, Eq, Sp,
            commonOperatorDefinition, Semi, Sp, conclusions);

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("B", type),
                Bound("A", familyType),
                Bound("velocity", familyType),
                Bound("t0", real),
            ],
            Implies(premises, letConclusion));
    }
}
