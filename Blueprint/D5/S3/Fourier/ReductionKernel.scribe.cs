using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class ReductionKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Fourier/ReductionKernel",
            "Reduction of a fourth-harmonic cotangent kernel to untwisted sine terms."),
        H("Cotangent Reduction Kernel"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-fourth-harmonic-cotangent-kernel-reduces-to-sine-terms"),
                H("The fourth-harmonic cotangent kernel reduces to sine terms"),
                LeanTheorem("D5/S3/Fourier/ReductionKernel.reduction_kernel"),
                Disp(Seq(
                    Forall, Sp, F.Id("x"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
                    Quad, Sp, Sin, Open, F.Id("x"), Close, Sp, Neq, Sp, D(0),
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("cos")), Open, D(4), F.Id("x"), Close, Cdot,
                    Frac,
                        Grp(Operatorname, Grp(F.Id("cos")), Open, F.Id("x"), Close),
                        Grp(Sin, Open, F.Id("x"), Close),
                    Sp, Eq, Sp,
                    Frac,
                        Grp(Operatorname, Grp(F.Id("cos")), Open, F.Id("x"), Close),
                        Grp(Sin, Open, F.Id("x"), Close),
                    Sp, Minus, Sp, D(2), Sin, Open, D(2), F.Id("x"), Close,
                    Sp, Minus, Sp, Sin, Open, D(4), F.Id("x"), Close, Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Writing cotangent as cosine divided by sine, the nonzero denominator permits field reduction. Double-angle identities then show that both sides equal the same cubic expression in cosine times sine.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-kernel-reduction-holds-at-golden-ratio-multiples"),
                H("The kernel reduction holds at golden-ratio multiples"),
                LeanTheorem("D5/S3/Fourier/ReductionKernel.reduction_kernel_golden"),
                Disp(Seq(
                    Forall, Sp, F.Id("k"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
                    Quad, Sp, Sin, Open, Pi, Sp, F.Id("k"), Varphi, Close, Sp, Neq, Sp, D(0),
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("cos")), Open, D(4), Pi, Sp, F.Id("k"), Varphi, Close,
                    Cdot, Operatorname, Grp(F.Id("cot")), Open, Pi, Sp, F.Id("k"), Varphi, Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("cot")), Open, Pi, Sp, F.Id("k"), Varphi, Close,
                    Sp, Minus, Sp, D(2), Sin, Open, D(2), Pi, Sp, F.Id("k"), Varphi, Close,
                    Sp, Minus, Sp, Sin, Open, D(4), Pi, Sp, F.Id("k"), Varphi, Close, Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Specializing the universal identity at pi times an integer times the golden ratio yields the literal cotangent-kernel form under its nonzero-sine hypothesis.")))
            ))));
}
