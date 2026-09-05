using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenTransferFourfoldCharacterizationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenTransferFourfoldCharacterization."
        + "golden_transfer_fourfold_characterization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four independent transfer and orbit conditions characterize the golden ratio.",
        H("Golden Transfer Fourfold Characterization"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-transfer-fourfold-characterization"),
            DeclarationHandle.Create(Declaration),
            H("The golden transfer data and shortest orbit agree uniquely"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The sharp disk radius is phi, and the positive fixed point of the first "
                        + "inverse branch is phi minus one, equivalently phi inverse. Its local "
                        + "derivative has magnitude phi to the minus two, while the golden axis "
                        + "exponential scale is phi to the minus four.")),
                Paragraph(Text(
                    "Every integral hyperbolic trace has absolute value at least three. "
                        + "Monotonicity and injectivity of arcosh therefore make the trace-three "
                        + "golden axis shortest, with equality exactly at absolute trace three.")),
                Paragraph(Text(
                    "For every candidate radius greater than one, each of the sharp-domain, "
                        + "fixed-point, observed-derivative, and shortest-orbit scale conditions "
                        + "holds exactly when that candidate is phi.")),
                Paragraph(Text(
                    "Repository and pinned-library searches found the three imported partial "
                        + "owners and the required arcosh order lemmas, but no existing theorem "
                        + "stating the integral-trace minimum and fourfold characterization."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula one = D(1), two = D(2), three = D(3), four = D(4);
        Formula phiInverse = Power(Varphi, Seq(Minus, one));
        Formula phiInverseSquared = Power(Varphi, Seq(Minus, two));
        Formula phiInverseFourth = Power(Varphi, Seq(Minus, four));
        Formula ell = Multiply(
            two,
            Call("arcosh", new Formula.Fraction(three, two)));

        Formula sharpRadius = Call("IsLUB", RadiusSet(F.Id("r")), Varphi);
        Formula reciprocal = Equal(Subtract(Varphi, one), phiInverse);
        Formula fixedPoint = ForAll(
            "x",
            real,
            Implies(
                Less(D(0), F.Id("x")),
                Iff(
                    Equal(Apply(Branch(), F.Id("x")), F.Id("x")),
                    Equal(F.Id("x"), phiInverse))));
        Formula derivative = Equal(
            new Formula.Absolute(Call(
                "deriv", Branch(), Subtract(Varphi, one))),
            phiInverseSquared);
        Formula orbitScale = Equal(Call("exp", Neg(ell)), phiInverseFourth);

        Formula traceAbs = new Formula.Absolute(F.Id("t"));
        Formula traceLength = Multiply(
            two,
            Call("arcosh", new Formula.Fraction(traceAbs, two)));
        Formula shortestTrace = ForAll(
            "t",
            integers,
            Implies(
                Less(two, traceAbs),
                All(
                    LessOrEqual(ell, traceLength),
                    Iff(Equal(ell, traceLength), Equal(traceAbs, three)))));

        Formula r = F.Id("r");
        Formula candidateFixedPoint = Apply(Branch(), Subtract(r, one));
        Formula candidateCharacterizations = ForAll(
            "r",
            real,
            Implies(
                Less(one, r),
                All(
                    Iff(Call("IsLUB", RadiusSet(F.Id("s")), r), Equal(r, Varphi)),
                    Iff(Equal(candidateFixedPoint, Subtract(r, one)), Equal(r, Varphi)),
                    Iff(
                        Equal(
                            new Formula.Absolute(Call(
                                "deriv", Branch(), Subtract(r, one))),
                            phiInverseSquared),
                        Equal(r, Varphi)),
                    Iff(
                        Equal(Call("exp", Neg(ell)), Power(r, Seq(Minus, four))),
                        Equal(r, Varphi)))));

        return Disp(All(
            sharpRadius,
            reciprocal,
            fixedPoint,
            derivative,
            orbitScale,
            shortestTrace,
            candidateCharacterizations));
    }

    private static Formula RadiusSet(Formula radius) => new Formula.SetBuilder(
        All(
            LessOrEqual(D(1), radius),
            Less(radius, D(2)),
            Less(
                new Formula.Fraction(D(1), Subtract(D(2), radius)),
                Add(D(1), radius))),
        radius,
        Seq(Mathbb, Grp(F.Id("R"))));

    private static Formula Branch()
    {
        Formula y = F.Id("y");
        return Seq(Open, y, Sp, Mapsto, Sp,
            new Formula.Fraction(D(1), Add(y, D(1))), Close);
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [Bound(name, domain)], body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Neg(Formula value) => Seq(Minus, value);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] formulas) => formulas.Aggregate(
        (left, right) => new Formula.Logic(left, FormulaLogicOperator.And, right));
}
