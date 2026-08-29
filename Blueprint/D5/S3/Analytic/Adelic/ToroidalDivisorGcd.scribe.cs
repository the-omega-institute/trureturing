using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ToroidalDivisorGcdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise nonvanishing analytic twists identify the zero divisor of xi "
            + "with the pointwise infimum of its normalized toroidal-period divisors.",
        H("Toroidal Divisor GCD"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("toroidal-divisor-gcd"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/ToroidalDivisorGcd.toroidal_divisor_gcd"),
                H("Xi is the divisor-gcd of normalized toroidal periods"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The normalized period family is constructed directly as the "
                            + "canonical xi reading times an analytic twist; it is not an "
                            + "additional primitive or a factorization premise.")),
                    Paragraph(Text(
                        "Analytic vanishing order is additive on each product. Pointwise "
                            + "nonvanishing supplies one twist of order zero, while every "
                            + "other product order is bounded below by the xi order.")),
                    Paragraph(Text(
                        "The first conclusion is the prescribed order identity at rho. The "
                            + "second states the corresponding divisor identity at every "
                            + "complex point, with indexed infimum representing pointwise gcd."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula complex = Call("Complex");
        Formula indexType = F.Id("Index");
        Formula rho = F.Id("rho");
        Formula twist = F.Id("T");
        Formula index = F.Id("i");
        Formula point = F.Id("s");
        Formula familyType = Arrow(indexType, Arrow(complex, complex));
        Formula xi = F.Id("xiReading");
        Formula twistAtPoint = Apply(Apply(twist, index), point);
        Formula periodFunction = Seq(xi, Sp, Times, Sp, Apply(twist, index));
        Formula periodOrderAtPoint = Call("analyticOrderAt", periodFunction, point);
        Formula xiOrderAtPoint = Call("analyticOrderAt", xi, point);
        Formula indexedPeriodOrder = Call("iInf", index, periodOrderAtPoint);

        Formula twistDifferentiable = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Call("Differentiable", complex, Apply(twist, index)));
        Formula pointwiseNonvanishing = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            new Formula.BindMany(
                FormulaQuantifier.Exists,
                [Bound("i", indexType)],
                NotEqualTo(twistAtPoint, D(0))));
        Formula premises = And(twistDifferentiable, pointwiseNonvanishing);

        Formula orderAtRho = EqualTo(
            Call("analyticOrderAt", xi, rho),
            Call(
                "iInf",
                index,
                Call(
                    "analyticOrderAt",
                    Seq(xi, Sp, Times, Sp, Apply(twist, index)),
                    rho)));
        Formula divisorIdentity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            EqualTo(xiOrderAtPoint, indexedPeriodOrder));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("rho", complex),
                Bound("T", familyType),
            ],
            Implies(premises, And(orderAtRho, divisorIdentity))));
    }
}
