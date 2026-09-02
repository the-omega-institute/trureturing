using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class PositiveFredholmLimitZerosDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Locally uniform limits of finite positive spectral determinants have only nonpositive real zeros.",
        H("Positive Fredholm Limits Preserve the Negative Real Zero Locus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-fredholm-limits-preserve-the-negative-real-zero-locus"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Isolation/PositiveFredholmLimitZeros."
                    + "positive_fredholm_limit_zeros"),
                H("Positive spectral determinant limits preserve their zero locus"),
                StatementSource.FromAuthor(StatementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite rank and every indexed nonnegative real spectrum, form "
                        + "the determinant polynomial as the product of the factors one plus the "
                        + "complex argument times an eigenvalue. If these polynomials converge "
                        + "locally uniformly on the complex plane, every zero of the limit has "
                        + "zero imaginary part and nonpositive real part.")),
                    Paragraph(Text(
                        "The normalization at zero is automatic from the displayed spectral "
                        + "product and local uniform convergence, so the Lean statement proves a "
                        + "strictly stronger form without adding that redundant premise.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found locally uniform limit "
                        + "regularity and analytic isolated-zero theorems, but no existing theorem "
                        + "that preserves this zero locus. The proof instead compares each "
                        + "off-axis factor with the same factor on a suitable positive real point. "
                        + "Boundedness at that point supplies a positive lower bound at the "
                        + "candidate zero, contradicting convergence there."))),
                DescribeRole.Theorem))));

    private static Formula StatementFormula()
    {
        Formula n = F.Id("N");
        Formula j = F.Id("j");
        Formula w = F.Id("w");
        Formula rank = F.Id("r");
        Formula eigenvalue = F.LambdaLower;
        Formula limit = F.Id("F");
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula complexes = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula rankAtN = Call(rank, n);
        Formula finiteIndex = Call(F.Id("Fin"), rankAtN);
        Formula eigenvalueAt = Call(eigenvalue, n, j);
        Formula factor = F.Grp(F.Seq(
            F.D(1), F.Sp, F.Plus, F.Sp, w, F.Sp, F.Cdot, F.Sp, eigenvalueAt));
        Formula determinant = F.Seq(
            F.Prod, F.Underscore,
            F.Grp(j, F.InMacro, F.Sp, finiteIndex), F.Sp, factor);
        Formula family = F.Seq(
            F.Open, n, F.Comma, F.Sp, w, F.Close,
            F.Sp, F.Mapsto, F.Sp, determinant);
        Formula positivity = F.Seq(
            F.Forall, F.Sp, n, F.InMacro, F.Sp, naturals, F.Comma, F.Sp,
            F.Forall, F.Sp, j, F.InMacro, F.Sp, finiteIndex, F.Comma, F.Sp,
            F.D(0), F.Sp, F.Le, F.Sp, eigenvalueAt);
        Formula convergence = Call(
            F.Id("TendstoLocallyUniformly"), family, limit, F.Id("atTop"));
        Formula zeroLocus = F.Seq(
            F.Forall, F.Sp, w, F.InMacro, F.Sp, complexes, F.Comma, F.Sp,
            Call(limit, w), F.Sp, F.Eq, F.Sp, F.D(0), F.Sp,
            F.Rightarrow, F.Sp,
            F.Grp(F.Seq(
                Call(F.Id("Im"), w), F.Sp, F.Eq, F.Sp, F.D(0), F.Sp,
                F.Land, F.Sp,
                Call(F.Id("Re"), w), F.Sp, F.Le, F.Sp, F.D(0))));

        return F.Disp(F.Seq(
            F.Forall, F.Sp,
            rank, F.Colon, F.Sp, naturals, F.Sp, F.To, F.Sp, naturals,
            F.Comma, F.Sp, RowBreak, F.Grp(),
            eigenvalue, F.Colon, F.Sp,
            F.Grp(n, F.Colon, F.Sp, naturals), F.Sp, F.To, F.Sp,
            finiteIndex, F.Sp, F.To, F.Sp, reals,
            F.Comma, F.Sp, RowBreak, F.Grp(),
            limit, F.Colon, F.Sp, complexes, F.Sp, F.To, F.Sp, complexes,
            F.Comma, F.Sp, RowBreak, F.Grp(),
            F.Grp(F.Seq(
                F.Grp(positivity), F.Sp, F.Land, F.Sp, F.Grp(convergence))),
            F.Sp, F.Rightarrow, F.Sp, RowBreak, F.Grp(), zeroLocus, F.Dot));
    }

    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
