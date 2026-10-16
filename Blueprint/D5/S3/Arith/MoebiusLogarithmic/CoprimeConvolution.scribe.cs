using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.MoebiusLogarithmic;

internal sealed class CoprimeConvolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/MoebiusLogarithmic/CoprimeConvolution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Summing over all prime-power divisors supported on a modulus enforces coprimality.",
        H("The finite coprimality convolution"),
        Blocks(
            Describe.Lean(DescribeId.Create("prime-support"),
                DeclarationHandle.Create(Prefix + "PrimeSupported"),
                H("Unrestricted prime exponents"), StatementSource.FromAuthor(SupportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Supported(q,n) means that every prime dividing n "
                    + "divides q. No bound is imposed on any exponent in n. The value at "
                    + "n=1 is true, since there are no prime divisors of one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coprime-coefficient"),
                DeclarationHandle.Create(Prefix + "sum_supported_moebius"),
                H("The exact coefficient identity"), StatementSource.FromAuthor(ConvolutionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum is over positive divisors d of n whose "
                    + "prime support is contained in that of q. Its coefficient is the "
                    + "actual integer Moebius value mu(n/d). At a prime power p^k, "
                    + "a prime dividing q allows every exponent from zero through k, "
                    + "and Moebius cancellation makes the sum zero when k is positive. "
                    + "For a prime outside q only d=1 remains. Multiplicativity then "
                    + "gives exactly mu(n) on integers coprime to q and zero elsewhere. "
                    + "For n=1 both sides are one. Nat.divisors 0 is empty, and mu(0)=0, "
                    + "so the identity also holds at zero."))), DescribeRole.Theorem))));

    private static Formula SupportFormula()
    {
        var q = F.Id("q"); var n = F.Id("n"); var p = F.Id("p");
        return Disp(Seq(Forall, Sp, q, Comma, n, InMacro,
            Seq(Mathbb, Grp(F.Id("N"))), Comma,
            Call("Supported", q, n), Leftrightarrow, Sp,
            Forall, Sp, p, InMacro, Seq(Mathbb, Grp(F.Id("N"))), Comma,
            Call("Prime", p), Land, Sp, Call("Divides", p, n), Rightarrow, Sp, Call("Divides", p, q)));
    }

    private static Formula ConvolutionFormula()
    {
        var q = F.Id("q"); var n = F.Id("n"); var d = F.Id("d");
        Formula left = Seq(new Formula.Subscript(Sum,
            Seq(d, InMacro, Sp, Call("divisors", n), Comma, Call("Supported", q, d))),
            Call("mu", new Formula.Fraction(n, d)));
        return Disp(Seq(Forall, Sp, q, Comma, n, InMacro,
            Seq(Mathbb, Grp(F.Id("N"))), Comma,
            Equal(left, Call("ite", Equal(Call("gcd", n, q), D(1)), Call("mu", n), D(0)))));
    }
}
