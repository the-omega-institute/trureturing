using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class PositiveDeterminantCoefficientCompactnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficientwise limits of positive finite matrix determinants converge locally uniformly and retain their zero locus.",
        H("Positive Determinant Coefficient Compactness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-determinant-coefficient-compactness"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Isolation/PositiveDeterminantCoefficientCompactness."
                    + "positive_determinant_coefficient_compactness"),
                H("Positive determinant coefficients determine the compact limit"),
                StatementSource.FromAuthor(StatementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each index, the source positive finite-rank operator is represented "
                        + "on its finite range by a positive semidefinite complex matrix. The "
                        + "coefficient premise is displayed for the determinant polynomial "
                        + "itself, with the target coefficient given by the corresponding "
                        + "Taylor derivative of the entire function.")),
                    Paragraph(Text(
                        "The first coefficient bounds the traces eventually. Positivity and the "
                        + "spectral factorization then bound every determinant on each circle by "
                        + "one exponential constant. Cauchy estimates and dominated convergence "
                        + "of the Taylor series yield locally uniform convergence.")),
                    Paragraph(Text(
                        "The public conclusion retains both clauses: locally uniform convergence "
                        + "of the determinant family and the nonpositive real location of every "
                        + "zero of the normalized limit."))),
                DescribeRole.Theorem))));

    private static Formula StatementFormula()
    {
        Formula n = F.Id("N");
        Formula m = F.Id("m");
        Formula w = F.Id("w");
        Formula rank = F.Id("r");
        Formula matrixFamily = F.Id("A");
        Formula limit = F.Id("Q");
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula complexes = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula rankAtN = Call(rank, n);
        Formula finiteIndex = Call(F.Id("Fin"), rankAtN);
        Formula matrixType = Call(F.Id("Matrix"), finiteIndex, finiteIndex, complexes);
        Formula matrixAtN = Call(matrixFamily, n);
        Formula determinantAt = Call(
            F.Id("det"),
            F.Seq(F.D(1), F.Sp, F.Plus, F.Sp, w, F.Sp, F.Cdot, F.Sp, matrixAtN));
        Formula determinantFamily = F.Seq(
            F.Open, n, F.Comma, F.Sp, w, F.Close,
            F.Sp, F.Mapsto, F.Sp, determinantAt);
        Formula positivity = F.Seq(
            F.Forall, F.Sp, n, F.InMacro, F.Sp, naturals,
            F.Comma, F.Sp, Call(F.Id("PosSemidef"), matrixAtN));
        Formula differentiability = Call(F.Id("Differentiable"), complexes, limit);
        Formula normalization = F.Seq(Call(limit, F.D(0)), F.Sp, F.Eq, F.Sp, F.D(1));
        Formula coefficientAt = Call(
            F.Id("coefficient"),
            m,
            F.Seq(
                F.Open, w, F.Sp, F.Mapsto, F.Sp,
                Call(
                    F.Id("det"),
                    F.Seq(
                        F.D(1), F.Sp, F.Plus, F.Sp,
                        w, F.Sp, F.Cdot, F.Sp, matrixAtN)),
                F.Close));
        Formula taylorCoefficient = F.Seq(
            Call(F.Id("inv"), F.Seq(F.Open, m, F.Bang, F.Close)),
            F.Sp, F.Cdot, F.Sp,
            Call(F.Id("iteratedDeriv"), m, limit, F.D(0)));
        Formula coefficientConvergence = F.Seq(
            F.Forall, F.Sp, m, F.InMacro, F.Sp, naturals,
            F.Comma, F.Sp,
            Call(
                F.Id("Tendsto"),
                F.Seq(F.Open, n, F.Close, F.Sp, F.Mapsto, F.Sp, coefficientAt),
                F.Id("atTop"),
                taylorCoefficient));
        Formula localConvergence = Call(
            F.Id("TendstoLocallyUniformly"),
            determinantFamily,
            limit,
            F.Id("atTop"));
        Formula zeroLocus = F.Seq(
            F.Forall, F.Sp, w, F.InMacro, F.Sp, complexes,
            F.Comma, F.Sp,
            Call(limit, w), F.Sp, F.Eq, F.Sp, F.D(0),
            F.Sp, F.Rightarrow, F.Sp,
            F.Grp(F.Seq(
                Call(F.Id("Im"), w), F.Sp, F.Eq, F.Sp, F.D(0),
                F.Sp, F.Land, F.Sp,
                Call(F.Id("Re"), w), F.Sp, F.Le, F.Sp, F.D(0))));
        Formula premises = F.Grp(F.Seq(
            F.Grp(positivity), F.Sp, F.Land, F.Sp,
            F.Grp(differentiability), F.Sp, F.Land, F.Sp,
            F.Grp(normalization), F.Sp, F.Land, F.Sp,
            F.Grp(coefficientConvergence)));
        Formula conclusions = F.Grp(F.Seq(
            F.Grp(localConvergence), F.Sp, F.Land, F.Sp,
            F.Grp(zeroLocus)));

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
            premises, F.Sp, F.Rightarrow, F.Sp, RowBreak, F.Grp(),
            conclusions, F.Dot));
    }

    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
