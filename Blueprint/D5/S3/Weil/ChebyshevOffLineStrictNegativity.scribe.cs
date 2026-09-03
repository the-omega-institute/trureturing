using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class ChebyshevOffLineStrictNegativityDocument
    : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/ChebyshevOffLineStrictNegativity."
            + "chebyshev_off_line_strict_negativity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive Chebyshev degree gives a strictly negative slack at a "
            + "genuine off-line squared distance.",
        H("Chebyshev Off-Line Strict Negativity"),
        Blocks(Describe.Lean(
            DescribeId.Create("chebyshev-off-line-strict-negativity"),
            DeclarationHandle.Create(Handle),
            H("Positive degrees are strictly negative off line"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a positive scale and a nonzero transverse displacement whose "
                        + "square lies below the scale, the compact coordinate is minus "
                        + "the hyperbolic cosine of the displayed rapidity.")),
                Paragraph(Text(
                    "The rapidity is twice artanh of the absolute normalized displacement. "
                        + "Mathlib's Chebyshev parity and hyperbolic evaluation identities "
                        + "then turn the slack into minus sinh squared, which is strict for "
                        + "positive degree.")),
                Paragraph(Text(
                    "For every nonnegative input, the same compactification lies in the "
                        + "closed unit interval and its Chebyshev slack lies in [0,1]. "
                        + "The Lean module separately records equality at zero degree and "
                        + "zero displacement."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula degree = F.Id("N");
        Formula scale = F.Id("a");
        Formula input = F.Id("x");
        Formula delta = DeltaLower;
        Formula variable = F.Id("y");
        Formula deltaSquared = Square(delta);
        Formula kappa = Kappa;
        Formula coordinate = new Formula.Subscript(F.Id("u"), scale);
        Formula slack = new Formula.Subscript(F.Id("W"), Seq(degree, Comma, scale));
        Formula offLine = new Formula.Negate(deltaSquared);
        Formula offCoordinate = Apply(coordinate, offLine);
        Formula onCoordinate = Apply(coordinate, input);
        Formula rapidity = Call(
            "arcosh",
            new Formula.Fraction(Add(scale, deltaSquared), Subtract(scale, deltaSquared)));
        Formula normalizedDistance = new Formula.Fraction(
            Seq(Lvert, delta, Rvert),
            Seq(Sqrt, Grp(scale)));
        Formula hyperbolicArgument = Product(degree, kappa);
        Formula chebyshev = new Formula.Subscript(F.Id("T"), degree);
        Formula premises = Seq(
            D(0), Sp, Lt, Sp, degree,
            Sp, Land, Sp, D(0), Sp, Lt, Sp, scale,
            Sp, Land, Sp, D(0), Sp, Le, Sp, input,
            Sp, Land, Sp, delta, Sp, Neq, Sp, D(0),
            Sp, Land, Sp, deltaSquared, Sp, Lt, Sp, scale);

        return Disp(new Formula.Aligned([
            Seq(Apply(coordinate, variable), Sp, Eq, Sp,
                new Formula.Fraction(Subtract(variable, scale), Add(variable, scale)),
                Comma, Sp, Apply(slack, variable), Sp, Eq, Sp,
                Subtract(D(1), Square(Apply(chebyshev, Apply(coordinate, variable)))), Comma),
            Seq(Forall, Sp, degree, Sp, InMacro, Sp, NaturalNumbers(), Comma, Sp,
                scale, Comma, Sp, input, Comma, Sp, delta, Sp, InMacro, Sp,
                RealNumbers(), Comma),
            Seq(premises, Sp, Rightarrow, Sp, kappa, Sp, Eq, Sp, rapidity, Comma),
            Seq(offCoordinate, Sp, Eq, Sp, Minus, Call("cosh", kappa),
                Sp, Land, Sp, kappa, Sp, Eq, Sp,
                Product(D(2), Call("artanh", normalizedDistance)), Comma),
            Seq(Apply(chebyshev, offCoordinate), Sp, Eq, Sp,
                Product(Power(Grp(Minus, D(1)), degree), Call("cosh", hyperbolicArgument)),
                Comma),
            Seq(Apply(slack, offLine), Sp, Eq, Sp,
                Minus, Square(Call("sinh", hyperbolicArgument)), Sp, Lt, Sp, D(0), Comma),
            Seq(onCoordinate, Sp, InMacro, Sp,
                ClosedInterval(Grp(Minus, D(1)), D(1)),
                Sp, Land, Sp, Apply(slack, input), Sp, InMacro, Sp,
                ClosedInterval(D(0), D(1)), Dot),
        ]));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Call(string name, Formula argument) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, argument, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Square(Formula value) => Power(value, D(2));

    private static Formula ClosedInterval(Formula left, Formula right) =>
        Seq(OpenBracket, left, Comma, Sp, right, CloseBracket);

    private static Formula NaturalNumbers() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula RealNumbers() => Seq(Mathbb, Grp(F.Id("R")));
}
