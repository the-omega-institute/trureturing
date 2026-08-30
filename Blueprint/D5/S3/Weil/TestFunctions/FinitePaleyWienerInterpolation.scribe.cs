using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class FinitePaleyWienerInterpolationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite conjugation-compatible data admit an exact compact smooth Hermitian "
            + "Fourier-Laplace interpolant.",
        H("Finite Paley-Wiener Interpolation"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-paley-wiener-interpolation"),
            DeclarationHandle.Create(
                "D5/S3/Weil/TestFunctions/FinitePaleyWienerInterpolation."
                    + "finite_exact_paley_wiener_interpolation"),
            H("Finite exact Paley-Wiener interpolation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "A normalized compact bump is dilated until its Fourier-Laplace transform "
                    + "is nonzero at every prescribed node. Lagrange interpolation then "
                    + "constructs the polynomial differential multiplier, and integration "
                    + "by parts proves its public transform factorization.")),
                Paragraph(Text(
                    "Conjugate reflection of the raw test preserves the common compact "
                    + "support window and supplies the Hermitian real structure. The "
                    + "compatibility of the node values makes the symmetrized transform "
                    + "retain every prescribed value."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Natural"), real = Call("Real"), complex = Call("Complex");
        Formula infinity = Call("infinity"), imaginaryUnit = Call("I");
        Formula m = F.Id("M"), z = F.Id("z"), r = F.Id("r");
        Formula conjugateIndex = F.Id("conjIndex");
        Formula j = F.Id("j"), k = F.Id("k"), x = F.Id("x"), w = F.Id("w");
        Formula length = F.Id("L"), seed = F.Id("psi"), polynomial = F.Id("P");
        Formula raw = F.Id("raw"), test = F.Id("f");

        Formula finiteIndex = Call("Fin", m);
        Formula nodeFamily = new Formula.TypeArrow(finiteIndex, complex);
        Formula functionType = new Formula.TypeArrow(real, complex);
        Formula polynomialType = Call("Polynomial", complex);
        Formula window = Call("Ioo", new Formula.Negate(length), length);

        Formula Transform(Formula function, Formula point) =>
            Call("fourierLaplace", function, point);
        Formula At(Formula function, Formula argument) => Apply(function, argument);
        Formula Node(Formula index) => At(z, index);
        Formula Value(Formula index) => At(r, index);
        Formula Conjugate(Formula value) => Call("conj", value);
        Formula Smooth(Formula function) => Call("ContDiff", real, infinity, function);
        Formula Compact(Formula function) => Call("HasCompactSupport", function);
        Formula InWindow(Formula function) =>
            Subset(Call("tsupport", function), window);

        Formula conjugateNode = ForAll(
            [Bound("j", finiteIndex)],
            Equal(Node(At(conjugateIndex, j)), Conjugate(Node(j))));
        Formula conjugateValue = ForAll(
            [Bound("j", finiteIndex)],
            Equal(Value(At(conjugateIndex, j)), Conjugate(Value(j))));
        Formula assumptions = All(
            Call("Injective", z),
            conjugateNode,
            conjugateValue);

        Formula seedNonzero = ForAll(
            [Bound("j", finiteIndex)],
            NotEqual(Transform(seed, Node(j)), D(0)));
        Formula interpolationPolynomial = ForAll(
            [Bound("j", finiteIndex)],
            Equal(
                Call("eval", polynomial, Node(j)),
                Div(Value(j), Transform(seed, Node(j)))));
        Formula iteratedDerivative =
            Call("iterate", F.Id("deriv"), k, seed);
        Formula rawTerm = Mul(
            Mul(
                Call("coeff", polynomial, k),
                Pow(new Formula.Negate(imaginaryUnit), k)),
            At(iteratedDerivative, x));
        Formula rawDefinition = Equal(
            raw,
            Lambda(
                x,
                real,
                Call("sum", k, Call("support", polynomial), rawTerm)));
        Formula rawFactorization = ForAll(
            [Bound("w", complex)],
            Equal(
                Transform(raw, w),
                Mul(Call("eval", polynomial, w), Transform(seed, w))));
        Formula symmetrizedDefinition = Equal(
            test,
            Lambda(
                x,
                real,
                Div(
                    Add(At(raw, x), Conjugate(At(raw, new Formula.Negate(x)))),
                    D(2))));
        Formula hermitian = ForAll(
            [Bound("x", real)],
            Equal(At(test, new Formula.Negate(x)), Conjugate(At(test, x))));
        Formula exactInterpolation = ForAll(
            [Bound("j", finiteIndex)],
            Equal(Transform(test, Node(j)), Value(j)));

        Formula conclusion = Exists(
            [
                Bound("L", real),
                Bound("psi", functionType),
                Bound("P", polynomialType),
                Bound("raw", functionType),
                Bound("f", functionType),
            ],
            All(
                Less(D(0), length),
                Smooth(seed),
                Compact(seed),
                InWindow(seed),
                seedNonzero,
                interpolationPolynomial,
                rawDefinition,
                Smooth(raw),
                Compact(raw),
                InWindow(raw),
                rawFactorization,
                symmetrizedDefinition,
                Smooth(test),
                Compact(test),
                InWindow(test),
                hermitian,
                exactInterpolation));

        return Disp(ForAll(
            [
                Bound("M", natural),
                Bound("z", nodeFamily),
                Bound("r", nodeFamily),
                Bound("conjIndex", new Formula.TypeArrow(finiteIndex, finiteIndex)),
            ],
            Implies(assumptions, conclusion)));
    }

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Seq(Open, variable, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Pow(Formula value, Formula exponent) =>
        Call("pow", value, exponent);

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
