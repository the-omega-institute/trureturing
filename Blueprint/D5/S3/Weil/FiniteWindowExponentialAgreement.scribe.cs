using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class FiniteWindowExponentialAgreementDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/FiniteWindowExponentialAgreement."
            + "finite_window_exponential_agreement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hyperbolic budget tubes force uniform exponential agreement on every fixed window.",
        H("Finite-Window Exponential Agreement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-window-exponential-agreement"),
                DeclarationHandle.Create(Declaration),
                H("Every fixed window agrees at the hyperbolic exponential rate"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The hypotheses are the same bounded-correlation and local cosh "
                            + "difference law used by the frozen hyperbolic budget tube. "
                            + "Positivity of the scale and resolvent excludes the totalized "
                            + "sinh denominator at zero.")),
                    Paragraph(Text(
                        "The two tube walls bound both signs of the budget deviation by "
                            + "R-star divided by sinh(aL) squared. Monotonicity of cosh in "
                            + "absolute value then makes the bound independent of time on "
                            + "the fixed window.")),
                    Paragraph(Text(
                        "For sufficiently large L, exp(aL)/4 is at most sinh(aL). This gives "
                            + "one time-independent constant multiplying exp(-2aL); when "
                            + "a is one half, the exponent simplifies exactly to -L."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula rate = F.Id("a");
        Formula center = new Formula.Subscript(F.Id("R"), Star);
        Formula window = F.Id("T");
        Formula scale = F.Id("L");
        Formula time = F.Id("t");
        Formula constant = F.Id("C");
        Formula error = Call("DeltaH", scale, time);
        Formula cschEnvelope = Product(
            new Formula.Fraction(center, Square(Call("sinh", Product(rate, scale)))),
            Call("cosh", Product(rate, window)));
        Formula fixedWindow = Seq(
            Forall, Sp, scale, Comma, Sp, D(0), Sp, Lt, Sp, scale,
            Comma, Sp, window, Sp, Lt, Sp, Product(D(2), scale),
            Sp, Rightarrow, Sp, Forall, Sp, time, Comma, Sp,
            new Formula.Absolute(time), Sp, Le, Sp, window,
            Sp, Rightarrow, Sp, new Formula.Absolute(error), Sp, Le, Sp,
            cschEnvelope);
        Formula generalDecay = Seq(
            Exists, Sp, constant, Sp, Geq, Sp, D(0), Comma, Sp,
            Call("eventually", scale, Seq(
                Forall, Sp, time, Comma, Sp, new Formula.Absolute(time), Sp, Le, Sp,
                window, Sp, Rightarrow, Sp, new Formula.Absolute(error), Sp, Le, Sp,
                Product(constant, Call("exp", Seq(Minus, Product(D(2), rate, scale)))))));
        Formula halfDecay = Seq(
            rate, Sp, Eq, Sp, new Formula.Fraction(D(1), D(2)),
            Sp, Rightarrow, Sp, Exists, Sp, constant, Sp, Geq, Sp, D(0),
            Comma, Sp, Call("eventually", scale, Seq(
                Forall, Sp, time, Comma, Sp, new Formula.Absolute(time), Sp, Le, Sp,
                window, Sp, Rightarrow, Sp, new Formula.Absolute(error), Sp, Le, Sp,
                Product(constant, Call("exp", Seq(Minus, scale))))));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, rate, Comma, Sp, center, Comma, Sp, window,
                Sp, InMacro, Sp, RealNumbers(), Comma),
            Seq(D(0), Sp, Lt, Sp, rate, Sp, Land, Sp, D(0), Sp, Le, Sp,
                center, Sp, Land, Sp, D(0), Sp, Le, Sp, window,
                Sp, Land, Sp, Call("BoundedLocalCoshLaw", rate, center),
                Sp, Rightarrow),
            Seq(Open, fixedWindow, Close, Sp, Land),
            Seq(Open, generalDecay, Close, Sp, Land, Sp,
                Open, halfDecay, Close, Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Product(params Formula[] factors)
    {
        var items = new List<Formula>();
        for (var index = 0; index < factors.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Cdot, Sp]);
            items.Add(factors[index]);
        }

        return Seq([.. items]);
    }

    private static Formula Square(Formula value) => new Formula.Power(value, D(2));

    private static Formula RealNumbers() => Seq(Mathbb, Grp(F.Id("R")));
}
