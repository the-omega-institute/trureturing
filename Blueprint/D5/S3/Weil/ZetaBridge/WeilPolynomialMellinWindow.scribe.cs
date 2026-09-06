using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilPolynomialMellinWindowDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.";
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula a = F.Id("a"), m = F.Id("m"), r = F.Id("r"), x = F.Id("x");
        Formula M = F.Id("M"), d = F.Id("d"), A = F.Id("A"), z = F.Id("z");
        Formula rate = Call("mellinRate", r, z);
        Formula atom = Call("mellinMonomial", a, m, r, x);
        Formula window = Call("polynomialMellinWindow", a, M, d, A);
        Formula endpoint = Call("div", Seq(
            Call("exp", Call("mul", rate, Seq(a, Minus, Call("log", m)))), Minus,
            Call("exp", Call("mul", rate, Seq(Minus, a)))), rate);
        return DocumentDefinition.Create(ScribeNode.Create(
            "An actual finite polynomial arithmetic Mellin window has an integrable "
                + "complex Fourier kernel and an exact finite endpoint transform.",
            H("Polynomial Mellin Window"),
            Blocks(
                Paragraph(Text(
                    "This source reuses Zeta23.paperFT with kernel exp(i*z*x). For "
                    + "h(t)=sum_{r<d} A_r*t^(2*r), the arithmetic window is "
                    + "4*exp(x/2)*sum_{1<=m<=M, m*exp(x)<=exp(a)} h(m*exp(x)) "
                    + "on [-a,a], with zero extension. The chosen Ioc endpoints "
                    + "give the same Lebesgue Fourier transform. The finite polynomial "
                    + "is a concrete approximation of the regular prolate modes, "
                    + "whose independent spectral certification is explained in the theory volume.")),
                Describe.Lean(DescribeId.Create("mellin-rate"),
                    DeclarationHandle.Create(Owner + "mellinRate"), H("Fourier-shifted monomial rate"),
                    StatementSource.FromAuthor(Disp(Seq(rate, Eq,
                        Call("add", Call("mul", D(2), r), Call("div", D(1), D(2)),
                            Call("mul", F.Id("i"), z))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("r is natural and z complex; the exponent is 2*r+1/2+i*z."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("mellin-monomial"),
                    DeclarationHandle.Create(Owner + "mellinMonomial"), H("One arithmetic monomial"),
                    StatementSource.FromAuthor(Disp(Seq(atom, Eq,
                        Call("IndicatorIoc", Seq(Minus, a), Seq(a, Minus, Call("log", m)),
                            Call("mul", Call("pow", m, Call("mul", D(2), r)),
                                Call("exp", Call("mul", Call("mellinRate", r, D(0)), x))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The formula uses a real interval and a complex exponential. It is specified before any Fourier evaluation."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("polynomial-mellin-window"),
                    DeclarationHandle.Create(Owner + "polynomialMellinWindow"), H("Finite polynomial arithmetic synthesis"),
                    StatementSource.FromAuthor(Disp(Seq(Call("apply", window, x), Eq,
                        Call("mul", D(4), Call("SumIcc", D(1), M,
                            Call("SumRange", d, Call("mul", Call("apply", A, r), atom))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The sums are over m=1,...,M and r=0,...,d-1. The factor four matches the calibrated Xi Mellin normalization in the existing volume."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("mellin-monomial-polynomial-value"),
                    DeclarationHandle.Create(Owner + "mellin_monomial_polynomial_value"), H("Exact polynomial identity"),
                    StatementSource.FromAuthor(Disp(Seq(atom, Eq,
                        Call("IndicatorIoc", Seq(Minus, a), Seq(a, Minus, Call("log", m)),
                            Call("mul", Call("exp", Call("div", x, D(2))),
                                Call("pow", Call("mul", m, Call("exp", x)), Call("mul", D(2), r))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The exponential form equals exp(x/2)*(m*exp(x))^(2*r) on the actual support. The proof uses exponential addition and natural powers; the half-power is retained."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("polynomial-mellin-fourier-integrable"),
                    DeclarationHandle.Create(Owner + "polynomial_mellin_fourier_integrable"), H("Actual Fourier integrability"),
                    StatementSource.FromAuthor(Disp(Call("Integrable", Call("mul",
                        Call("apply", window, x), Call("exp", Call("mul", F.Id("i"), z, x)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For every real a, natural M,d, complex coefficient family A and complex z, the actual Fourier integrand is integrable. Compact interval continuity proves each summand integrable, followed by finite linearity. This excludes totalized nonintegrable Fourier values."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("polynomial-mellin-window-paperFT"),
                    DeclarationHandle.Create(Owner + "polynomial_mellin_window_paperFT"), H("Quadrature-free Fourier evaluation"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("And", Call("ForAllIcc", D(1), M, Call("LessEqual", Call("log", m), Call("mul", D(2), a))),
                            Call("Less", Call("Im", z), Call("div", D(1), D(2)))), Rightarrow,
                        Call("paperFT", window, z), Eq,
                        Call("mul", D(4), Call("SumIcc", D(1), M, Call("SumRange", d,
                            Call("mul", Call("apply", A, r), Call("pow", m, Call("mul", D(2), r)), endpoint))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Assume log(m)<=2*a for each included positive integer m and Im(z)<1/2. "
                        + "Every rate has positive real part, so no denominator is zero. "
                        + "The proof identifies the Fourier integrand on each arithmetic interval, "
                        + "uses the existing complex-exponential integral theorem, and interchanges "
                        + "only finite sums with proved integrable summands. No quadrature hypothesis "
                        + "or unknown prolate/Weil eigenvector is supplied. The numerical consumer "
                        + "independently certifies prolate eigenpairs and their complete Legendre tail. "
                        + "The all-scale arithmetic ground-model comparison remains open; this "
                        + "source does not prove the prolate spectral theorem, Xi convergence or RH."))),
                    DescribeRole.Theorem))));
    }
}
