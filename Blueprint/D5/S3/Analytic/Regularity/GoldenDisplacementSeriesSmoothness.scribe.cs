using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Regularity;

internal sealed class GoldenDisplacementSeriesSmoothnessDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden displacement sum is smooth at every point of its exact convergence region.",
        H("Golden Displacement Series Smoothness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-smoothness"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Regularity/GoldenDisplacementSeriesSmoothness."
                    + "golden_displacement_series_contDiffOn_infty"),
                H("The displacement sum is smooth on its convergence region"),
                StatementSource.FromAuthor(SmoothnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The proof uses contDiffOn_infty to fix a finite order k and then works "
                        + "at an arbitrary parameter pair in the convergence region. The two "
                        + "strict affine constraints provide a positive delta. The proof lowers "
                        + "both coordinates by (k+1) times delta to obtain a corner point whose "
                        + "dTerm family is summable, and it works on the open quadrant above the "
                        + "point obtained by lowering both coordinates by delta. Because delta "
                        + "carries the factor 1/(k+1), that corner and its summable dTerm family "
                        + "are the same at every order; what depends on k is delta, the open "
                        + "quadrant, and the scalar factors (2/delta)^j.")),
                    Paragraph(Text(
                        "For a positive index n, the term is exp composed with a continuous "
                        + "linear functional ell(n), with coefficients -log(nS(n)) and -log(n). "
                        + "ContinuousLinearMap.iteratedFDeriv_comp_right expresses its jth "
                        + "Frechet derivative as the jth one-variable derivative of exp composed "
                        + "with ell(n) in every argument. The norm comparison for that composition, "
                        + "norm_iteratedFDeriv_eq_norm_iteratedDeriv, and Real.iter_deriv_exp give "
                        + "a bound by dTerm at the variable point times the jth power of the norm "
                        + "of ell(n).")),
                    Paragraph(Text(
                        "The real logarithm estimate log(x) <= x^delta/delta is used only for "
                        + "natural bases at least one. Nonnegativity of log at those bases converts "
                        + "the logarithm to its norm, and natural-power monotonicity raises the "
                        + "resulting nonnegative inequality. Coordinatewise real-power monotonicity "
                        + "gives non-strict bounds on the quadrant. Since j <= k, the j powers of "
                        + "both bases are absorbed by the gap between the quadrant and the corner. "
                        + "The norm of the nth jth-derivative continuous multilinear map is at "
                        + "most (2/delta)^j times the nth value of the summable corner-term family.")),
                    Paragraph(Text(
                        "At index zero, the summand and every iterated derivative used by the proof "
                        + "are zero. At index one, dTerm is one, nS(1) is one, and both logarithms "
                        + "vanish; hence every positive-order derivative term is zero, while the "
                        + "order-zero bound compares the constant term with the corner term, also "
                        + "one. At order zero, continuousOn_tsum uses the summable corner-term "
                        + "family directly and does not infer continuity from pointwise summability.")),
                    Paragraph(Text(
                        "A private localized finite-order sum lemma supplies the missing "
                        + "multivariable local form of Mathlib's global smooth-series theorem. Its "
                        + "zero case is continuousOn_tsum. In the successor case, "
                        + "hasFDerivAt_tsum_of_isPreconnected identifies the derivative of the sum, "
                        + "norm_iteratedFDeriv_fderiv shifts the derivative bounds by one order, "
                        + "and the induction hypothesis applies to the family of Frechet "
                        + "derivatives. Local congruence identifies that derivative series with "
                        + "fderiv of the original sum. This proves every finite order at the chosen "
                        + "point, and contDiffOn_infty yields smoothness on the exact region.")),
                    Paragraph(Text(
                        "The theorem does not claim real analyticity of order omega, complex "
                        + "analyticity or continuation, a published formula for any iterated "
                        + "derivative or Hessian, one derivative majorant valid for every order, "
                        + "a majorant uniform near the convergence-region boundary, or strict "
                        + "termwise decrease."))),
                DescribeRole.Theorem))));

    private static Formula SmoothnessFormula()
    {
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula domain = F.Seq(real, F.Sp, F.Times, F.Sp, real);
        Formula first = F.Seq(p, F.Dot, F.D(1));
        Formula second = F.Seq(p, F.Dot, F.D(2));
        Formula term = Call("dTerm", first, second, n);
        Formula series = F.Seq(
            F.Sum, F.Underscore, F.Grp(n, F.Eq, F.D(0)),
            F.Caret, F.Grp(F.Infty), F.Sp, term);
        Formula sumFunction = F.Seq(
            p, F.Sp, F.Colon, F.Sp, domain, F.Sp, F.Mapsto, F.Sp, series);
        Formula convergenceRegion = SetOf(
            p,
            domain,
            Call("Summable", Call("dTerm", first, second)));

        return F.Disp(Call(
            "ContDiffOn",
            real,
            F.Infty,
            sumFunction,
            convergenceRegion));
    }

    private static Formula SetOf(Formula point, Formula domain, Formula predicate) =>
        F.Seq(
            F.Left, F.OpenBrace, point, F.Sp, F.Colon, F.Sp, domain,
            F.Sp, F.Mid, F.Sp, predicate, F.Right, F.CloseBrace);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
