using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CenteredDisjointPrincipalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CenteredDisjointPrincipal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The constant part of the centered even factors identifies a principal coefficient and a controlled error.",
        H("Centered principal coefficient and signed remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("centered-principal-remainder"),
                DeclarationHandle.Create(Owner + ".centered_principal_remainder"),
                H("Amplitude and squared-norm errors"),
                StatementSource.FromAuthor(LocalStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For finite T and complex phases a(j), exponential parameter c and natural "
                        + "degree d≥|T|, set n=d−|T|, u=c−(sum of a(j) over T)/2, and v=(sum of |a(j)|² over T)/24. "
                        + "Let C be the degree-d coefficient of exp(cx) times the product over T of exp(−a(j)x)−1. "
                        + "Write A for the product of |a(j)| over T, H for the degree-n coefficient of exp(|u|x+v x²), "
                        + "and h=|u|^n/n!. The principal coefficient P is the product of −a(j) over T times u^n/n!.")),
                    Paragraph(Text("Extract the linear factors from the centered product. The even factors all have "
                        + "constant coefficient one, so the coefficientwise quadratic majorant remains valid after "
                        + "subtracting one from both products. Multiplication by the centered exponential and extraction "
                        + "of degree n give the difference H−h and the amplitude error. For the square-norm difference, "
                        + "the reverse triangle inequality bounds the difference of norms and the full majorant bounds "
                        + "their sum. Multiplying produces the difference of squares H²−h²."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixed-centered-principal-error"),
                DeclarationHandle.Create(Owner + ".mixed_centered_principal_error"),
                H("Signed coefficient approximation"),
                StatementSource.FromAuthor(MixedStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a finite ambient set s, choose c to be the sum of its phases and let Q be the "
                        + "disjoint product of exp(a(j)x)+exp(conj(a(j))y)−1. For each subset T with |T|≤d, define "
                        + "the corresponding P(T), A(T), H(T) and h(T) by the local theorem.")),
                    Paragraph(Text("The exact mixed coefficient is the alternating sum of squared overlap norms. "
                        + "Subtract the alternating sum of squared principal norms and apply the triangle inequality "
                        + "termwise. This gives the sum of the local squared error bounds. The actual high-degree "
                        + "arithmetic estimate for zeta ordinates still requires control of the subset centers and "
                        + "the signed principal sum."))),
                DescribeRole.Theorem))));

    private static Formula LocalStatement()
    {
        var c = F.Id("C");
        var p = F.Id("P");
        var a = F.Id("A");
        var h = F.Id("H");
        var small = F.Id("h");
        return Disp(new Formula.Aligned([
            Seq(Amp, Bar, c, Minus, p, Bar, Sp, Le, Sp, a, Open, h, Minus, small, Close),
            Seq(Amp, Bar, SquareNorm(c), Minus, SquareNorm(p), Bar, Sp, Le, Sp,
                new Formula.Power(a, D(2)), Open, new Formula.Power(h, D(2)), Minus,
                new Formula.Power(small, D(2)), Close)]));
    }

    private static Formula SquareNorm(Formula x) => new Formula.Power(Seq(Bar, x, Bar), D(2));

    private static Formula MixedStatement()
    {
        var t = F.Id("T");
        var d = F.Id("d");
        var sum = new Formula.Subscript(Sum, Seq(t, Sp, Subseteq, Sp, F.Id("s"), Comma,
            Bar, t, Bar, Sp, Le, Sp, d));
        var sign = new Formula.Power(Seq(Open, Minus, D(1), Close), Seq(Bar, t, Bar));
        var coeff = Seq(OpenBracket, new Formula.Power(F.Id("x"), d), new Formula.Power(F.Id("y"), d),
            CloseBracket, F.Id("Q"));
        return Disp(new Formula.Aligned([
            Seq(Amp, Bar, Call("Re", coeff), Minus, sum, sign, SquareNorm(Call("P", t)), Bar, Sp, Le),
            Seq(Amp, Quad, sum, new Formula.Power(Call("A", t), D(2)), Open,
                new Formula.Power(Call("H", t), D(2)), Minus, new Formula.Power(Call("h", t), D(2)), Close)]));
    }
}
