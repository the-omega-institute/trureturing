using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class CompleteLowHGaussianMomentDocument : IScribeDocumentDefinition
{
    private static Formula Real => Seq(Mathbb, Grp(StrataLint.Scribe.FormulaDsl.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(StrataLint.Scribe.FormulaDsl.Id("C")));

    private static Formula CallF(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula AddF(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula SubF(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula MulF(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Pow(Formula value, long exponent) =>
        new Formula.Power(value, Num(exponent));

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Neg(Formula value) => SubF(Num(0), value);

    private static Formula Exp(Formula value) => CallF("exp", value);

    private static Formula Sqrt(Formula value) => CallF("sqrt", value);

    private static Formula OfReal(Formula value) => CallF("ofReal", value);

    private static Formula ExplicitIntegral()
    {
        var m = StrataLint.Scribe.DefinitionDsl.Id("m");
        var gamma = StrataLint.Scribe.DefinitionDsl.Id("gamma");
        var z = StrataLint.Scribe.DefinitionDsl.Id("z");
        var y = StrataLint.Scribe.DefinitionDsl.Id("y");
        var shifted = SubF(y, MulF(Num(16), m));
        var coordinate = Div(SubF(y, MulF(Num(16), m)), MulF(Num(2), m));
        var polynomial = MulF(
            AddF(y, Num(1)),
            AddF(AddF(Pow(coordinate, 2), Pow(gamma, 2)), Num(1)));
        var density = Div(
            MulF(polynomial,
                Exp(Div(Neg(Pow(shifted, 2)), MulF(Num(4), m)))),
            Sqrt(MulF(MulF(Num(4), CallF("pi")), m)));
        var integrand = MulF(OfReal(density), Exp(MulF(z, OfReal(y))));
        return CallF("integral", y, Real, integrand);
    }

    private static Formula ExplicitRhs()
    {
        var m = StrataLint.Scribe.DefinitionDsl.Id("m");
        var gamma = StrataLint.Scribe.DefinitionDsl.Id("gamma");
        var z = StrataLint.Scribe.DefinitionDsl.Id("z");
        var tilted = AddF(AddF(MulF(Num(16), m), MulF(MulF(Num(2), m), z)), Num(1));
        var quadratic = AddF(AddF(Pow(z, 2), Pow(gamma, 2)),
            AddF(Num(1), Div(Num(1), MulF(Num(2), m))));
        var exponent = AddF(MulF(m, Pow(z, 2)), MulF(MulF(Num(16), m), z));
        return MulF(AddF(MulF(tilted, quadratic), MulF(Num(2), z)), Exp(exponent));
    }

    private static Formula ExplicitStatement()
    {
        var m = StrataLint.Scribe.DefinitionDsl.Id("m");
        var gamma = StrataLint.Scribe.DefinitionDsl.Id("gamma");
        var z = StrataLint.Scribe.DefinitionDsl.Id("z");
        return All("m", Real,
            All("gamma", Real,
                All("z", Complex,
                    Imp(new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, m),
                        Eq(ExplicitIntegral(), ExplicitRhs())))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized cubic Gaussian moment is an exact identity for every complex parameter.",
        H("Complete Low-Height Gaussian Moment"),
        Blocks(
            Paragraph(Text(
                "The normalized Gaussian has center 16*m and variance 2*m. Transport from the "
                + "Gaussian probability measure proves integrability of every tilted monomial. "
                + "The entire complex MGF and its first three derivatives evaluate the four density "
                + "moments needed for the cubic polynomial.")),
            Paragraph(Text(
                "The linear combination of those moments gives the exact covariance correction "
                + "+2*z. This identity supplies the physical full-line moment for the countable "
                + "weighted mean, with arbitrary real gamma and arbitrary complex exponential tilt.")),
            Describe.Lean(
                DescribeId.Create("complete-low-h-gaussian-moment"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/CompleteLowHGaussianMoment.cubic_gaussian_moment_explicit"),
                H("Exact normalized cubic Gaussian moment"),
                StatementSource.FromAuthor(Disp(ExplicitStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real m with 0 < m, arbitrary real gamma, and arbitrary complex z, "
                        + "the displayed real density integral equals the displayed complex polynomial "
                        + "times exp(m*z^2 + 16*m*z). The polynomial retains the tilted center "
                        + "16*m + 2*m*z + 1, the term 1/(2*m), and the explicit +2*z covariance "
                        + "correction. The preceding cubic_gaussian_moment theorem gives the same "
                        + "identity through the named density moments; this Describe records the "
                        + "expanded author statement without introducing a wrapper.")),
                    Paragraph(Text(
                        "The applicability boundary is exactly m > 0, gamma in the reals, and z in the "
                        + "complexes. No height, strip, finite family, spectral mean, Robin, QGP, or RH "
                        + "premise is added. The Mathlib Gaussian and complex-MGF results are analytic "
                        + "inputs; they are not certificate fields or computational utility.")))))));
}
