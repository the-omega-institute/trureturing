using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class PositiveFredholmLimitZerosDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Locally uniform limits of determinants of finite-rank positive operators have only nonpositive real zeros.",
        H("Positive Fredholm Limits Preserve the Negative Real Zero Locus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-matrix-determinants-factor-over-the-spectrum"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Isolation/PositiveFredholmLimitZeros."
                    + "positive_matrix_det_factorization"),
                H("Positive matrix determinants factor over the spectrum"),
                StatementSource.FromAuthor(FactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A positive semidefinite complex matrix is the finite-range model of a "
                        + "finite-rank positive operator. The matrix spectral theorem diagonalizes "
                        + "it by a unitary change of basis. Determinant multiplicativity cancels "
                        + "the unitary factors and leaves the product of one plus the complex "
                        + "argument times each real eigenvalue."))),
                DescribeRole.Theorem),
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
                        "For every index, the source operator is represented on its finite range "
                        + "by a positive semidefinite Hermitian matrix. Its approximating function "
                        + "is publicly the determinant of the identity plus the complex argument "
                        + "times that matrix. If these determinants converge locally uniformly, "
                        + "and the limit is normalized to one at zero, every zero of the limit has "
                        + "zero imaginary part and nonpositive real part.")),
                    Paragraph(Text(
                        "The public factorization bridge rewrites each determinant as the finite "
                        + "product over the matrix eigenvalues. Positive semidefiniteness makes "
                        + "those eigenvalues nonnegative. The locally uniform limit argument then "
                        + "compares every off-axis factor with a suitable positive real point; "
                        + "boundedness there prevents a zero away from the nonpositive real axis.")),
                    Paragraph(Text(
                        "The normalization at zero is displayed as a premise exactly as in the "
                        + "source statement and excludes zero itself as a zero of the limit."))),
                DescribeRole.Theorem))));

    private static Formula FactorizationFormula()
    {
        Formula rank = F.Id("r");
        Formula j = F.Id("j");
        Formula w = F.Id("w");
        Formula matrix = F.Id("A");
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula complexes = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula finiteIndex = Call(F.Id("Fin"), rank);
        Formula matrixType = Call(F.Id("Matrix"), finiteIndex, finiteIndex, complexes);
        Formula eigenvalueAt = Call(F.Id("eigenvalue"), matrix, j);
        Formula factor = F.Grp(F.Seq(
            F.D(1), F.Sp, F.Plus, F.Sp, w, F.Sp, F.Cdot, F.Sp, eigenvalueAt));
        Formula product = F.Seq(
            F.Prod, F.Underscore,
            F.Grp(j, F.InMacro, F.Sp, finiteIndex), F.Sp, factor);
        Formula identityPlus = F.Seq(
            F.D(1), F.Sp, F.Plus, F.Sp, w, F.Sp, F.Cdot, F.Sp, matrix);
        Formula determinant = Call(F.Id("det"), identityPlus);

        return F.Disp(F.Seq(
            F.Forall, F.Sp,
            rank, F.Colon, F.Sp, naturals,
            F.Comma, F.Sp, RowBreak, F.Grp(),
            matrix, F.Colon, F.Sp, matrixType,
            F.Comma, F.Sp, RowBreak, F.Grp(),
            w, F.Colon, F.Sp, complexes,
            F.Comma, F.Sp, RowBreak, F.Grp(),
            Call(F.Id("PosSemidef"), matrix),
            F.Sp, F.Rightarrow, F.Sp, RowBreak, F.Grp(),
            determinant, F.Sp, F.Eq, F.Sp, product, F.Dot));
    }

    private static Formula StatementFormula()
    {
        Formula n = F.Id("N");
        Formula w = F.Id("w");
        Formula rank = F.Id("r");
        Formula matrixFamily = F.Id("A");
        Formula limit = F.Id("F");
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula complexes = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula rankAtN = Call(rank, n);
        Formula finiteIndex = Call(F.Id("Fin"), rankAtN);
        Formula matrixType = Call(F.Id("Matrix"), finiteIndex, finiteIndex, complexes);
        Formula matrixAtN = Call(matrixFamily, n);
        Formula identityPlus = F.Seq(
            F.D(1), F.Sp, F.Plus, F.Sp, w, F.Sp, F.Cdot, F.Sp, matrixAtN);
        Formula determinant = Call(F.Id("det"), identityPlus);
        Formula family = F.Seq(
            F.Open, n, F.Comma, F.Sp, w, F.Close,
            F.Sp, F.Mapsto, F.Sp, determinant);
        Formula positivity = F.Seq(
            F.Forall, F.Sp, n, F.InMacro, F.Sp, naturals,
            F.Comma, F.Sp, Call(F.Id("PosSemidef"), matrixAtN));
        Formula convergence = Call(
            F.Id("TendstoLocallyUniformly"), family, limit, F.Id("atTop"));
        Formula normalization = F.Seq(
            Call(limit, F.D(0)), F.Sp, F.Eq, F.Sp, F.D(1));
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
            matrixFamily, F.Colon, F.Sp,
            F.Grp(n, F.Colon, F.Sp, naturals), F.Sp, F.To, F.Sp,
            matrixType,
            F.Comma, F.Sp, RowBreak, F.Grp(),
            limit, F.Colon, F.Sp, complexes, F.Sp, F.To, F.Sp, complexes,
            F.Comma, F.Sp, RowBreak, F.Grp(),
            F.Grp(F.Seq(
                F.Grp(positivity), F.Sp, F.Land, F.Sp,
                F.Grp(convergence), F.Sp, F.Land, F.Sp,
                F.Grp(normalization))),
            F.Sp, F.Rightarrow, F.Sp, RowBreak, F.Grp(), zeroLocus, F.Dot));
    }

    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
