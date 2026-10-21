using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalIocFourierMassDocument : IScribeDocumentDefinition
{
    private const string MassOwner = "D5/S3/Weil/ZetaBridge/OriginalIocFourierMass.";

    private static Formula Call(string name, params Formula[] args)
    {
        var result = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq(result.ToArray());
    }

    private static Formula Sq(Formula x) => Seq(Grp(x), Caret, Grp(D(2)));


    public DocumentDefinition Create()
    {
        Formula L = F.Id("L"), N = F.Id("N"), n = F.Id("n"), s = F.Id("s");
        Formula f = F.Id("f"), z = F.Id("z"), u = F.Id("u"), v = F.Id("v");
        Formula mass = Call("OriginalMass", L, f);
        Formula signedMass = Call("tsum", Call("SignedCoeffSq", L, f));
        Formula density = Call("exteriorFourierDensity", L, N, u, v, s);
        Formula tailMass = Seq(Call("SquareMass", u), Plus, Call("SquareMass", v));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Original arbitrary complex Ioc L2 Fourier dictionary with literal dx mass.",
            H("Original Ioc Fourier Mass"),
            Blocks(
                Paragraph(Text(
                    "The original interval is Ioc(-L/2,L/2), with literal zero extension. "
                    + "The phase-adjusted signed basis is (-1)^n exp(i*2*pi*n*x/L)/sqrt(L). "
                    + "All coefficients are complex and all signed integer modes are retained. "
                    + "No periodic endpoint equality, real or even restriction, or finite upper "
                    + "mode cutoff is imposed. Scientific statements and proof scope are given "
                    + "by the referenced Lean declarations.")),
                Describe.Lean(
                    DescribeId.Create("ioc-zero-extension"),
                    DeclarationHandle.Create(MassOwner + "iocZeroExtend"),
                    H("Literal Ioc zero extension"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("iocZeroExtend", L, f), Eq,
                        Call("indicator", Call("Ioc", Seq(Minus, L, D(2)), Seq(L, D(2))), f)))),
                    AssessedProvenance.FromRepo(), Blocks(), DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("signed-parseval-mass"),
                    DeclarationHandle.Create(MassOwner + "tsum_signedCoeff_sq_eq_mass"),
                    H("Signed Parseval equals original dx mass"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Positive", L), Land, Sp, Call("MemLpIocTwo", L, f), Rightarrow, Sp,
                        signedMass, Eq, mass))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The proof directly consumes tsum_sq_fourierCoeffOn and "
                        + "multiplies by L. The resulting coefficients are the actual signed "
                        + "phase-adjusted inner products, and the right side remains the original "
                        + "restricted Lebesgue mass."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("resonance-safe-centered-integral"),
                    DeclarationHandle.Create(MassOwner + "integral_centered_exp"),
                    H("Centered exponential integral"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Positive", L), Rightarrow, Sp,
                        Call("IntegralCenteredExp", L, s), Eq,
                        Call("CenteredExpIntegral", L, s)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The zero-frequency branch is explicit. The nonzero branch uses the "
                        + "public interval exponential integral, so the rational form is only "
                        + "used away from resonance."))),
                    DescribeRole.Theorem))));
    }
}
