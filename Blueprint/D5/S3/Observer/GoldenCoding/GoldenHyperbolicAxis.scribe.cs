using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenHyperbolicAxisDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenHyperbolicAxis.golden_hyperbolic_axis";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden Mobius map has two fixed endpoints and an explicit hyperbolic axis length.",
        H("Golden Hyperbolic Axis and Observer Index"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-hyperbolic-axis"),
            DeclarationHandle.Create(Declaration),
            H("The golden map determines its axis and observer scale"),
            StatementSource.FromAuthor(AxisFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For g(z)=1+1/z, the fixed-point equation is the golden quadratic. "
                        + "The two real solutions are the golden ratio and its negative "
                        + "conjugate, and both are nonzero genuine fixed points.")),
                Paragraph(Text(
                    "The Fibonacci matrix has determinant minus one, while its square has "
                        + "determinant one and trace three. The endpoint circle in the upper "
                        + "half-plane is centered at one half with squared radius five fourths.")),
                Paragraph(Text(
                    "The trace formula reduces the translation length to four log phi. Its "
                        + "half-length is the logarithm of the observer index phi squared, and "
                        + "the decaying projective weight is phi to the minus two.")),
                Paragraph(Text(
                    "No projective-line action structure, hyperbolic-isometry classification, "
                        + "Jones projection, six-dimensional lattice, or Riemann-scattering "
                        + "claim is introduced, because the source does not supply formal "
                        + "definitions from which those narrative identifications follow."))),
            DescribeRole.Theorem))));

    private static Formula AxisFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula z = F.Id("z"), x = F.Id("x"), y = F.Id("y");
        Formula g = F.Id("g"), fibonacci = F.Id("F"), circle = F.Id("C");
        Formula phi = Varphi, phiPrime = Seq(Varphi, Apos);
        Formula ell = Ell;
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula threeHalves = new Formula.Fraction(D(3), D(2));
        Formula fiveFourths = new Formula.Fraction(D(5), D(4));
        Formula phiSquared = Power(phi, D(2));
        Formula phiInverse = Power(phi, Seq(Minus, D(1)));
        Formula phiInverseSquared = Power(phi, Seq(Minus, D(2)));
        Formula sqrtFiveOverTwo = new Formula.Fraction(Call("sqrt", D(5)), D(2));

        Formula fixedClassification = Equal(
            Call("Fix", g), new Formula.SetLiteral([phi, phiPrime]));
        Formula quadraticClassification = ForAll(
            "z",
            real,
            All(
                Iff(
                    Equal(Call("g", z), z),
                    Equal(Power(z, D(2)), Add(z, D(1)))),
                Iff(
                    Equal(Power(z, D(2)), Add(z, D(1))),
                    Or(Equal(z, phi), Equal(z, phiPrime)))));
        Formula conjugateForms = All(
            Equal(phiPrime, Sub(D(1), phi)),
            Equal(phiPrime, Neg(phiInverse)),
            NotEqual(phi, D(0)),
            NotEqual(phiPrime, D(0)));
        Formula secondIterate = ForAll(
            "z",
            real,
            Implies(
                All(NotEqual(z, D(0)), NotEqual(z, Neg(D(1)))),
                Equal(
                    Call("g", Call("g", z)),
                    new Formula.Fraction(Add(Mul(D(2), z), D(1)), Add(z, D(1))))));
        Formula matrixData = All(
            Equal(Call("det", fibonacci), Neg(D(1))),
            Equal(Power(fibonacci, D(2)), Call("matrix2", D(2), D(1), D(1), D(1))),
            Equal(Call("det", Power(fibonacci, D(2))), D(1)),
            Equal(Call("trace", Power(fibonacci, D(2))), D(3)));
        Formula circleEquation = ForAll(
            "x",
            real,
            ForAll(
                "y",
                real,
                Iff(
                    Call("C", x, y),
                    Equal(
                        Add(Power(Sub(x, half), D(2)), Power(y, D(2))),
                        fiveFourths))));
        Formula circleWitnesses = All(
            Call("C", phi, D(0)),
            Call("C", phiPrime, D(0)),
            Call("C", half, sqrtFiveOverTwo),
            Less(D(0), sqrtFiveOverTwo));
        Formula lengthData = All(
            Equal(ell, Mul(D(2), Call("arcosh", threeHalves))),
            Equal(ell, Mul(D(4), Call("log", phi))),
            Equal(new Formula.Fraction(ell, D(2)), Call("log", phiSquared)),
            Equal(Call("exp", Neg(new Formula.Fraction(ell, D(2)))), phiInverseSquared));
        Formula observerData = All(
            Equal(F.Id("observerIndex"), phiSquared),
            Equal(F.Id("projectionWeight"), phiInverseSquared),
            Equal(Call("abs", F.Id("goldenProjectiveMultiplier")), phiInverseSquared));
        Formula definitions = Seq(
            F.Id("let"), Sp, Call("g", z), Sp, Eq, Sp,
            Add(D(1), new Formula.Fraction(D(1), z)), Semi, Sp,
            F.Id("let"), Sp, fibonacci, Sp, Eq, Sp,
            Call("matrix2", D(1), D(1), D(1), D(0)), Semi, Sp,
            F.Id("let"), Sp, Call("C", x, y), Sp, Eq, Sp,
            Equal(
                Add(Power(Sub(x, half), D(2)), Power(y, D(2))),
                fiveFourths), Semi, Sp,
            All(
                fixedClassification,
                quadraticClassification,
                conjugateForms,
                secondIterate,
                matrixData,
                circleEquation,
                circleWitnesses,
                lengthData,
                observerData));

        return Disp(definitions);
    }

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)],
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Neg(Formula value) => Seq(Minus, value);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate(And);
}
