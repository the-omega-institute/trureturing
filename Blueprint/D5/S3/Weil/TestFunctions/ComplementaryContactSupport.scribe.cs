using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class ComplementaryContactSupportDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/TestFunctions/ComplementaryContactSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero complementary gap localizes residual support on entire contact zeros.",
        H("Complementary Contact Support"),
        Blocks(Describe.Lean(
            DescribeId.Create("complementary-contact-support"),
            DeclarationHandle.Create(Handle + "complementary_contact_support"),
            H("Complementary contact support"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The contact gap is constructed from the canonical Fourier-Laplace "
                        + "transform and the positive resolvent denominator. Pointwise "
                        + "nonnegativity and a zero integral force it to vanish throughout "
                        + "the residual support.")),
                Paragraph(Text(
                    "Clearing the denominator constructs the complex contact function. "
                        + "Compact support makes the transform entire and supplies an explicit "
                        + "finite exponential bound after multiplication by the quadratic "
                        + "factor.")),
                Paragraph(Text(
                    "Reality of the even test makes the transform real on the real axis, so "
                        + "the first support localization transfers to the real zeros of the "
                        + "entire contact function."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula complex = Call("Complex");
        Formula test = Call("WeilTestFunction");
        Formula a = F.Id("a"), theta = F.Id("theta"), phi = F.Id("phi");
        Formula mu = F.Id("mu"), x = F.Id("x"), xi = F.Id("xi"), z = F.Id("z");
        Formula contact = F.Id("S"), contactEntire = F.Id("G");
        Formula constant = F.Id("C"), rate = F.Id("tau");

        Formula Transform(Formula point) => Call("fourierLaplace", phi, point);
        Formula Denominator(Formula point) =>
            Add(Pow(point, D(2)), Pow(a, D(2)));
        Formula ContactAt(Formula point) =>
            Add(Call("realPart", Transform(point)), Div(theta, Denominator(point)));
        Formula EntireAt(Formula point) => Add(
            Mul(Denominator(point), Transform(point)),
            theta);
        Formula Lambda(Formula variable, Formula domain, Formula body) =>
            Seq(Open, variable, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);
        Formula Let(Formula name, Formula value) =>
            Seq(Operatorname, Grp(F.Id("let")), Sp, name, Sp, Eq, Sp, value);

        Formula realTest = ForAll(
            [Bound("x", real)],
            Equal(Call("conj", Apply(phi, x)), Apply(phi, x)));
        Formula contactNonnegative = ForAll(
            [Bound("xi", real)],
            LessEqual(D(0), ContactAt(xi)));
        Formula contactIntegrable = Call(
            "Integrable",
            Lambda(xi, real, ContactAt(xi)),
            mu);
        Formula complementarity = Equal(
            Call("integral", xi, real, ContactAt(xi), mu),
            D(0));
        Formula assumptions = All(
            Less(D(0), a),
            LessEqual(D(0), theta),
            realTest,
            contactNonnegative,
            contactIntegrable,
            complementarity);

        Formula contactDefinition = Let(
            contact,
            Lambda(xi, real, ContactAt(xi)));
        Formula entireDefinition = Let(
            contactEntire,
            Lambda(z, complex, EntireAt(z)));
        Formula contactZeroSet = new Formula.SetBuilder(
            Equal(Apply(contact, xi), D(0)),
            xi,
            real);
        Formula entireRealZeroSet = new Formula.SetBuilder(
            Equal(Apply(contactEntire, xi), D(0)),
            xi,
            real);
        Formula supportOnContact = Subset(
            Call("support", mu),
            contactZeroSet);
        Formula entire = Call("Differentiable", complex, contactEntire);
        Formula finiteType = Exists(
            [Bound("C", real), Bound("tau", real)],
            All(
                LessEqual(D(0), constant),
                LessEqual(D(0), rate),
                ForAll(
                    [Bound("z", complex)],
                    LessEqual(
                        Call("norm", Apply(contactEntire, z)),
                        Mul(
                            constant,
                            Call(
                                "exp",
                                Mul(rate, Call("norm", z))))))));
        Formula supportOnEntireZeros = Subset(
            Call("support", mu),
            entireRealZeroSet);
        Formula conclusion = Seq(
            contactDefinition, Semi, Sp,
            entireDefinition, Semi, Sp,
            All(
            supportOnContact,
            entire,
            finiteType,
            supportOnEntireZeros));

        return Disp(ForAll(
            [
                Bound("a", real),
                Bound("theta", real),
                Bound("phi", test),
                Bound("mu", Call("Measure", real)),
            ],
            Implies(assumptions, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Subset(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
