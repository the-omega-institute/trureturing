using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ConvolutionSquareCriticalLineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric convolution-square zero cutoffs split into a nonnegative critical-line part "
            + "and an off-line remainder without asserting the Riemann hypothesis.",
        H("Convolution-Square Critical-Line Split"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("real-spectral-parameter-exactly-on-the-critical-line"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine."
                    + "gamma_im_eq_zero_iff_zero_on_critical_line"),
                H("The spectral parameter is real exactly on the critical line"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("Im")), Open,
                    F.Id("Z"), Dot, F.Id("gamma"), Open, F.Id("n"), Close, Close,
                    Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
                    Re, Open, F.Id("Z"), Dot, F.Id("zero"), Open, F.Id("n"), Close, Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("criticalAbscissa"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every index in supplied ZeroData, the imaginary part of its complex "
                    + "spectral parameter vanishes exactly when the corresponding zero has real "
                    + "part equal to the critical abscissa. This is an algebraic consequence of "
                    + "the frozen spectral-parameter definition and makes no claim that every "
                    + "zero satisfies the condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-line-zero-summand-is-real-and-nonnegative"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine."
                    + "critical_line_zero_summand_real_nonnegative"),
                H("A critical-line zero summand is real and nonnegative"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                    F.Id("g"), InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Re, Open, F.Id("Z"), Dot, F.Id("zero"), Open, F.Id("n"), Close, Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("criticalAbscissa")), Sp,
                    Rightarrow, Sp,
                    Operatorname, Grp(F.Id("Im")), Open,
                    Operatorname, Grp(F.Id("zeroSummand")), Open,
                    F.Id("Z"), Comma, Sp,
                    Operatorname, Grp(F.Id("convolutionSquare")), Open, F.Id("g"), Close,
                    Comma, Sp, F.Id("n"), Close, Close, Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    D(0), Sp, Leq, Sp,
                    Re, Open, Operatorname, Grp(F.Id("zeroSummand")), Open,
                    F.Id("Z"), Comma, Sp,
                    Operatorname, Grp(F.Id("convolutionSquare")), Open, F.Id("g"), Close,
                    Comma, Sp, F.Id("n"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the critical line, the preceding equivalence identifies gamma with its "
                    + "real part. The frozen convolution-square positivity theorem then makes the "
                    + "Fourier-Laplace factor real and nonnegative. Multiplication by the stored "
                    + "natural-number zero multiplicity preserves both conclusions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("critical-line-truncated-sum-is-real-and-nonnegative"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine."
                    + "critical_line_truncated_sum_real_nonnegative"),
                H("Every critical-line truncated sum is real and nonnegative"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                    F.Id("g"), InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    F.Id("T"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Operatorname, Grp(F.Id("Im")), Open,
                    Operatorname, Grp(F.Id("criticalPart")), Open,
                    F.Id("Z"), Comma, Sp, F.Id("g"), Comma, Sp, F.Id("T"), Close, Close,
                    Sp, Eq, Sp, D(0), Sp, Land, Sp, D(0), Sp, Leq, Sp,
                    Re, Open, Operatorname, Grp(F.Id("criticalPart")), Open,
                    F.Id("Z"), Comma, Sp, F.Id("g"), Comma, Sp, F.Id("T"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here criticalPart is the finite sum over symmetricIndices T filtered by "
                    + "real part equal to criticalAbscissa, with each term equal to zeroSummand "
                    + "of the convolution square. Complex real and imaginary parts commute with "
                    + "finite sums, so termwise realness and nonnegativity give the two claims."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-zero-sum-splits-into-critical-and-off-line-parts"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine."
                    + "truncated_zero_sum_critical_offline_split"),
                H("A finite zero sum splits into critical and off-line parts"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                    F.Id("g"), InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    F.Id("T"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Operatorname, Grp(F.Id("truncatedZeroSum")), Open,
                    F.Id("Z"), Comma, Sp,
                    Operatorname, Grp(F.Id("convolutionSquare")), Open, F.Id("g"), Close,
                    Comma, Sp, F.Id("T"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("criticalPart")), Open,
                    F.Id("Z"), Comma, Sp, F.Id("g"), Comma, Sp, F.Id("T"), Close,
                    Sp, Plus, Sp, Operatorname, Grp(F.Id("offlinePart")), Open,
                    F.Id("Z"), Comma, Sp, F.Id("g"), Comma, Sp, F.Id("T"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The criticalPart filter uses equality with criticalAbscissa and offlinePart "
                    + "uses its negation on the same symmetric finite index set. Mathlib's finite "
                    + "filter-complement identity partitions the complete truncated zero sum. "
                    + "No assertion is made about either filtered family converging separately."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("combined-split-tends-to-the-explicit-formula"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine."
                    + "critical_offline_split_tendsto_explicit_formula"),
                H("The combined split tends to the explicit-formula value"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
                    F.Id("g"), InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                    F.Id("hZero"), Comma, Sp, F.Id("hArch"), Comma, Sp,
                    Lim, Underscore, Grp(F.Id("T"), To, Infty), Sp,
                    Open, Operatorname, Grp(F.Id("criticalPart")), Open,
                    F.Id("Z"), Comma, Sp, F.Id("g"), Comma, Sp, F.Id("T"), Close,
                    Sp, Plus, Sp, Operatorname, Grp(F.Id("offlinePart")), Open,
                    F.Id("Z"), Comma, Sp, F.Id("g"), Comma, Sp, F.Id("T"), Close, Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("poleTerm")), Open,
                    Operatorname, Grp(F.Id("convolutionSquare")), Open, F.Id("g"), Close, Close,
                    Sp, Minus, Sp, Operatorname, Grp(F.Id("primeTerm")), Open,
                    Operatorname, Grp(F.Id("convolutionSquare")), Open, F.Id("g"), Close, Close,
                    Sp, Plus, Sp, Operatorname, Grp(F.Id("archimedeanTerm")), Open,
                    Operatorname, Grp(F.Id("convolutionSquare")), Open, F.Id("g"), Close,
                    Comma, Sp, F.Id("hArch"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assuming only the frozen symmetric-zero and archimedean convergence "
                    + "premises for the convolution square, the combined filtered expression is "
                    + "rewritten to truncatedZeroSum. Its existing limit and the Weil explicit "
                    + "formula identify the displayed pole-minus-prime-plus-archimedean value. "
                    + "The theorem supplies no separate convergence result for either filter and "
                    + "does not assert the Riemann hypothesis."))),
                DescribeRole.Theorem))));
}
