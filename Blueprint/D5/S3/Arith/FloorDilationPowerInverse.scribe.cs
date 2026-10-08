using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class FloorDilationPowerInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FloorDilationPowerInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dominant first coefficient controls inversion of a floor dilation transform.",
        H("Quantitative Floor Dilation Inversion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("floor-sum-power-inverse"),
                DeclarationHandle.Create(Prefix + "floorSum_power_inverse"),
                H("Every nonnegative power scale"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let b and f be arbitrary real sequences indexed by "
                        + "natural numbers. Let a, C and T be real numbers with a>=0 and C>=0. "
                        + "For every natural N, assume the sum of |b(d)| over 1<d<=N is "
                        + "at most T, and assume T<|b(1)|. For every positive natural N, "
                        + "assume the absolute transform sum over 0<d<=N is at most C N^a. "
                        + "The conclusion bounds |f(N)| by C N^a/(|b(1)|-T) at every "
                        + "positive natural cutoff. All powers with exponent a are real powers; "
                        + "N/d inside f is natural division, or floor(N/d).")),
                    Paragraph(Text("The tail hypothesis at N=1 gives T>=0, so the strict "
                        + "gap makes the denominator and |b(1)| positive. Set K=C/(|b(1)|-T) "
                        + "and induct strongly on N. Splitting off d=1 leaves only "
                        + "1<=floor(N/d)<N for 1<d<=N. The inductive estimate and a>=0 "
                        + "bound every smaller value by K N^a. The triangle inequality "
                        + "therefore gives |b(1)| |f(N)| <= (C+K T) N^a. "
                        + "The defining equation K(|b(1)|-T)=C absorbs the tail and "
                        + "allows cancellation of the positive head.")),
                    Paragraph(Text("The theorem includes a=0 and C=0, and permits a "
                        + "negative first coefficient. No hypothesis on f(0) is needed, "
                        + "because each division argument in a positive-cutoff sum is positive. "
                        + "It assumes a bound on the transform rather than a global bound "
                        + "on its input. This is a general estimate; it does not establish "
                        + "a Fibonacci reconstruction identity, a Mertens growth bound, "
                        + "the Robin inequality, or the Riemann hypothesis."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var b = F.Id("b"); var f = F.Id("f"); var a = F.Id("a");
        var c = F.Id("C"); var t = F.Id("T"); var n = F.Id("N"); var d = F.Id("d");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula abs(Formula x) => new Formula.Absolute(x);
        Formula power = new Formula.Power(n, a);
        Formula sum(Formula lower, Formula term) => Seq(
            new Formula.Subscript(Sum, Seq(lower, Lt, Sp, d, Le, Sp, n)), term);
        Formula tail = Seq(Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            sum(D(1), abs(Call("b", d))), Le, Sp, t);
        Formula transform = Seq(Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            D(0), Lt, Sp, n, Rightarrow, Sp,
            abs(sum(D(0), Seq(Call("b", d), Cdot,
                Call("f", new Formula.Floor(new Formula.Fraction(n, d)))))),
            Le, Sp, c, Cdot, Sp, power);
        Formula conclusion = Seq(Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            D(0), Lt, Sp, n, Rightarrow, Sp, abs(Call("f", n)), Le, Sp,
            new Formula.Fraction(c, Seq(abs(Call("b", D(1))), Minus, t)), Cdot, Sp, power);
        return Disp(Seq(Forall, Sp, b, Comma, f, Colon, Sp, naturals, To, Sp,
            reals, Comma, Sp, Forall, Sp, a, Comma, c, Comma, t, InMacro, Sp, reals,
            Comma, Sp, Open, D(0), Le, Sp, a, Land, Sp, D(0), Le, Sp, c, Land, Sp,
            Open, tail, Close, Land, Sp, t, Lt, Sp, abs(Call("b", D(1))), Land, Sp,
            Open, transform, Close, Close, Rightarrow, Sp, conclusion));
    }
}
