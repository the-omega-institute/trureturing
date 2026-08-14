using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ConvolutionSquareOffLineOrbitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugation and reflection organize off-line convolution-square zero summands into "
            + "four-point orbits and make every finite off-line cutoff real.",
        H("Convolution-Square Off-Line Orbits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conjugate-zero-summands-are-complex-conjugates"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits."
                    + "convolution_square_zero_summand_conjugation"),
                H("Conjugate zero summands are complex conjugates"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                    F.Id("g"), InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("zeroSummand")), Open,
                    F.Id("Z"), Comma, Sp,
                    Operatorname, Grp(F.Id("convolutionSquare")), Open, F.Id("g"), Close,
                    Comma, Sp, F.Id("Z"), Dot, F.Id("conjugation"), Open, F.Id("n"), Close,
                    Close, Sp, Eq, Sp, Overline, Grp(
                    Operatorname, Grp(F.Id("zeroSummand")), Open,
                    F.Id("Z"), Comma, Sp,
                    Operatorname, Grp(F.Id("convolutionSquare")), Open, F.Id("g"), Close,
                    Comma, Sp, F.Id("n"), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Conjugation sends the spectral parameter gamma to minus its complex "
                    + "conjugate and preserves the stored multiplicity. Evenness removes the "
                    + "minus sign, while the convolution square is fixed by the Weil "
                    + "involution. Fourier-Laplace involution covariance then gives the stated "
                    + "complex conjugation identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("off-line-four-point-orbit-sum-is-real"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits."
                    + "off_line_zero_orbit_sum_eq_four_mul_re"),
                H("An off-line four-point orbit sums to four times one real part"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                    F.Id("g"), InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("Z"), Dot, F.Id("conjugation"), Open, F.Id("n"), Close,
                    Sp, Neq, Sp, F.Id("n"), Sp, Land, Sp,
                    Re, Open, F.Id("Z"), Dot, F.Id("zero"), Open, F.Id("n"), Close, Close,
                    Sp, Neq, Sp, Operatorname, Grp(F.Id("criticalAbscissa")), Sp,
                    Rightarrow, Sp, Sum, Underscore, Grp(
                    F.Id("k"), InMacro, Sp, OpenBrace,
                    F.Id("n"), Comma, Sp,
                    F.Id("Z"), Dot, F.Id("reflection"), Open, F.Id("n"), Close, Comma, Sp,
                    F.Id("Z"), Dot, F.Id("conjugation"), Open, F.Id("n"), Close, Comma, Sp,
                    F.Id("Z"), Dot, F.Id("conjugation"), Open,
                    F.Id("Z"), Dot, F.Id("reflection"), Open, F.Id("n"), Close, Close,
                    CloseBrace), Operatorname, Grp(F.Id("zeroSummand")), Open,
                    F.Id("Z"), Comma, Sp,
                    Operatorname, Grp(F.Id("convolutionSquare")), Open, F.Id("g"), Close,
                    Comma, Sp, F.Id("k"), Close, Sp, Eq, Sp, D(4), Sp, Re, Open,
                    Operatorname, Grp(F.Id("zeroSummand")), Open,
                    F.Id("Z"), Comma, Sp,
                    Operatorname, Grp(F.Id("convolutionSquare")), Open, F.Id("g"), Close,
                    Comma, Sp, F.Id("n"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen zero-orbit cardinality theorem supplies distinctness of the "
                    + "four displayed indices under the explicit nonreal and off-line "
                    + "hypotheses. Reflection leaves each summand unchanged, and conjugation "
                    + "replaces it by its complex conjugate, so the orbit total is twice a "
                    + "number plus twice its conjugate, namely four times its real part. No "
                    + "sign or existence assertion is made."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-off-line-zero-cutoffs-are-real"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits."
                    + "off_line_truncated_sum_real"),
                H("Every finite off-line zero cutoff is real"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                    F.Id("g"), InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    F.Id("T"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Operatorname, Grp(F.Id("Im")), Open,
                    Operatorname, Grp(F.Id("offlinePart")), Open,
                    F.Id("Z"), Comma, Sp, F.Id("g"), Comma, Sp, F.Id("T"), Close, Close,
                    Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here offlinePart is the sum over symmetricIndices T filtered by real part "
                    + "unequal to criticalAbscissa, with convolution-square zeroSummand as its "
                    + "term. The filtered finite set is stable under the conjugation permutation. "
                    + "Reindexing by that permutation and applying summand covariance shows the "
                    + "sum equals its complex conjugate, so its imaginary part vanishes. The "
                    + "theorem states reality only, not nonnegativity."))),
                DescribeRole.Theorem))));
}
