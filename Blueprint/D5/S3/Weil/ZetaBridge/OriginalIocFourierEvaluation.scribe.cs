using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalIocFourierEvaluationDocument : IScribeDocumentDefinition
{
    private const string EvaluationOwner = "D5/S3/Weil/ZetaBridge/OriginalIocFourierEvaluation.";

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
            H("Original Ioc Fourier Evaluation"),
            Blocks(
                Paragraph(Text(
                    "The original interval is Ioc(-L/2,L/2), with literal zero extension. "
                    + "The phase-adjusted signed basis is (-1)^n exp(i*2*pi*n*x/L)/sqrt(L). "
                    + "All coefficients are complex and all signed integer modes are retained. "
                    + "No periodic endpoint equality, real or even restriction, or finite upper "
                    + "mode cutoff is imposed. Scientific statements and proof scope are given "
                    + "by the referenced Lean declarations.")),
                Describe.Lean(
                    DescribeId.Create("original-l2-integral-evaluation"),
                    DeclarationHandle.Create(EvaluationOwner + "hasSum_signedCoeff_mul_basisPaperFT"),
                    H("Bounded evaluation of the complete complex L2 expansion"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Positive", L), Land, Sp, Call("MemLpIocTwo", L, f),
                        Rightarrow, Sp,
                        Call("HasSum", Call("SignedCoeffTimesBasisFT", L, f),
                            Call("paperFT", Call("iocZeroExtend", L, f)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The original Ioc MemLp representative and the negative-exponent "
                        + "evaluation kernel are lifted literally to AddCircle. The latter has "
                        + "norm one and is in L2. HilbertBasis.hasSum_inner_mul_inner for the "
                        + "public fourierBasis gives an integral pairing identity. "
                        + "The proof identifies both inner products and cancels normalized Haar "
                        + "and the two signed phases. It uses no pointwise Fourier inversion "
                        + "or periodic endpoint condition."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("actual-coefficient-integral"),
                    DeclarationHandle.Create(EvaluationOwner + "signedCoeff_eq_integral"),
                    H("Signed coefficients are the actual dx inner products"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Positive", L), Rightarrow, Sp,
                        Call("signedCoeff", L, f, n), Eq,
                        Call("OriginalBasisInnerProduct", L, f, n)))),
                    AssessedProvenance.FromRepo(), Blocks(), DescribeRole.Theorem))));
    }
}
