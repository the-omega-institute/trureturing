using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalIocFourierTailDocument : IScribeDocumentDefinition
{
    private const string TailOwner = "D5/S3/Weil/ZetaBridge/OriginalIocFourierTail.";

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
            H("Original Ioc Fourier Tail"),
            Blocks(
                Paragraph(Text(
                    "The original interval is Ioc(-L/2,L/2), with literal zero extension. "
                    + "The phase-adjusted signed basis is (-1)^n exp(i*2*pi*n*x/L)/sqrt(L). "
                    + "All coefficients are complex and all signed integer modes are retained. "
                    + "No periodic endpoint equality, real or even restriction, or finite upper "
                    + "mode cutoff is imposed. Scientific statements and proof scope are given "
                    + "by the referenced Lean declarations.")),
                Describe.Lean(
                    DescribeId.Create("actual-tail-mass"),
                    DeclarationHandle.Create(TailOwner + "signedCoeff_tail_mass"),
                    H("Two actual ordered tails exhaust the original mass"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Positive", L), Land, Sp, Call("MemLpIocTwo", L, f), Land, Sp,
                        Call("LowSignedCoefficientsZero", L, N, f), Rightarrow, Sp,
                        Call("BothTailsSquareSummable", L, N, f), Land, Sp,
                        Call("ActualTailMassSum", L, N, f), Eq, mass))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "positiveTail and negativeTail select N+j+1 and -(N+j+1). "
                        + "The proof splits a summable integer series into nonnegative and "
                        + "negative-successor parts, pays their different shifts N+1 and N, "
                        + "and kills only genuine low coefficients. Parseval leaves the right "
                        + "side as the original dx integral of the squared norm."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("actual-plus-transform-exterior-series"),
                    DeclarationHandle.Create(TailOwner + "paperFT_eq_exteriorSeries"),
                    H("Literal PLUS transform is the signed exterior series"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Positive", L), Land, Sp, Call("Positive", N), Land, Sp,
                        Call("MemLpIocTwo", L, f), Land, Sp, Call("QuarterBand", N, s), Land, Sp,
                        Call("LowSignedCoefficientsZero", L, N, f), Rightarrow, Sp,
                        Call("paperFT", Call("iocZeroExtend", L, f),
                            Call("PhysicalFrequency", L, s)), Eq,
                        Call("SqrtLOverPiSin", L, s), Sp,
                        Call("exteriorSeries", N, Call("signedCoeff", L, f), s)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The resonance-safe sinc basis transform is proved first. In the "
                        + "quarter band, each remaining signed mode is separated from every "
                        + "pole. Integer sine translation cancels the basis phase. The positive "
                        + "tail has denominator N+s+j+1; the negative tail contributes the "
                        + "minus sign and denominator N-s+j+1. These are the actual complex "
                        + "coefficients, with no parity assumption."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("actual-density-identity"),
                    DeclarationHandle.Create(TailOwner + "norm_paperFT_sq_eq_exteriorFourierDensity"),
                    H("Original squared transform equals the public exterior density"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Positive", L), Land, Sp, Call("Positive", N), Land, Sp,
                        Call("MemLpIocTwo", L, f), Land, Sp, Call("QuarterBand", N, s), Land, Sp,
                        Call("LowSignedCoefficientsZero", L, N, f), Rightarrow, Sp,
                        Sq(Call("NormActualPaperFT", L, f, s)), Eq,
                        Call("exteriorFourierDensity", L, N,
                            Call("positiveTail", N, Call("signedCoeff", L, f)),
                            Call("negativeTail", N, Call("signedCoeff", L, f)), s)))),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Taking the squared complex norm of the exact signed transform identity gives the public density with the actual positive and negative tails."))), DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("original-physical-leakage"),
                    DeclarationHandle.Create(TailOwner + "original_low_frequency_mass"),
                    H("Physical leakage on the exact public quarter band"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Positive", N), Land, Sp, Call("Positive", L), Land, Sp,
                        Call("MemLpIocTwo", L, f), Land, Sp,
                        Call("LowSignedCoefficientsZero", L, N, f), Rightarrow, Sp,
                        Call("PhysicalBandIntegrable", L, N, f), Land, Sp,
                        Call("NormalizedPhysicalIntegral", L, N, f), Leq, Sp,
                        Seq(Call("div", D(4), Seq(D(3), Sp, Sq(F.Id("pi")))), Sp, mass)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The body consumes only the public "
                        + "WeilInfiniteComplementLeakage.infinite_complement_low_frequency_mass. "
                        + "Its band is abs(s) <= N/4. Substitution t=2*pi*s/L yields "
                        + "abs(t) <= pi*N/(2*L) and dt/(2*pi)=ds/L, with interval "
                        + "integrability transported explicitly. The constant is 4/(3*pi^2). "
                        + "No private Cauchy theorem, separate half band estimate, full Weil "
                        + "positivity, Schur conclusion, Robin statement or RH conclusion is used."))),
                    DescribeRole.Theorem))));
    }
}
