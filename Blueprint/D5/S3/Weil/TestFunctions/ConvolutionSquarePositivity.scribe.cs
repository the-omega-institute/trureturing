using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class ConvolutionSquarePositivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fourier transform of a Weil convolution square is a nonnegative real norm square.",
        H("Convolution-Square Positivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("angular-frequency-transform-matches-mathlib-fourier"),
                DeclarationHandle.Create("D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity.fourierLaplace_real_eq_fourier"),
                H("Angular frequency matches mathlib Fourier frequency"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("g"), Sp, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    Xi, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Operatorname, Grp(F.Id("fourierLaplace")), Open, F.Id("g"), Comma, Sp,
                    Xi, Close, Sp, Eq, Sp, Mathcal, Grp(F.Id("F")), Open, F.Id("g"), Close,
                    Open, Frac, Grp(Xi), Grp(D(2), Pi), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every Weil test function, the angular-frequency Fourier-Laplace transform at xi equals mathlib's real Fourier transform at xi divided by two pi. The theorem is the normalization bridge between the repository kernel and mathlib's Fourier convention."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("convolution-square-transform-is-a-norm-square"),
                DeclarationHandle.Create("D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity.fourierLaplace_convolutionSquare_real"),
                H("A convolution square transforms to a norm square"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("g"), Sp, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    Xi, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Operatorname, Grp(F.Id("fourierLaplace")), Open, F.Id("g"), Star,
                    Widetilde, Grp(F.Id("g")), Comma, Sp, Xi, Close, Sp, Eq, Sp,
                    Lvert, Operatorname, Grp(F.Id("fourierLaplace")), Open, F.Id("g"), Comma,
                    Sp, Xi, Close, Rvert, Caret, Grp(D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real-axis transform of g convolved with its Weil involution is the complex norm square of the transform of g. The proof applies mathlib's Fourier convolution theorem and converts the involution transform to complex conjugation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("convolution-square-transform-is-real-and-nonnegative"),
                DeclarationHandle.Create("D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity.fourierLaplace_convolutionSquare_real_nonnegative"),
                H("A convolution-square transform is real and nonnegative"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("g"), Sp, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    Xi, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Operatorname, Grp(F.Id("Im")), Open, Operatorname,
                    Grp(F.Id("fourierLaplace")), Open, F.Id("g"), Star, Widetilde,
                    Grp(F.Id("g")), Comma, Sp, Xi, Close, Close, Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    D(0), Sp, Leq, Sp, Re, Open, Operatorname, Grp(F.Id("fourierLaplace")),
                    Open, F.Id("g"), Star, Widetilde, Grp(F.Id("g")), Comma, Sp, Xi, Close,
                    Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Because the preceding identity is a real norm square, its imaginary part vanishes and its real part is nonnegative at every real frequency. This is the Fourier-side positivity kernel for convolution-square Weil tests."))),
                DescribeRole.Theorem))));
}
