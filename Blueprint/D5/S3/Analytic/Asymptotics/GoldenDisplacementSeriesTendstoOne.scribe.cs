using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class GoldenDisplacementSeriesTendstoOneDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden displacement series tends to one as its first parameter tends to infinity.",
        H("Golden Displacement Series Limit at Infinity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-tendsto-one"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Asymptotics/GoldenDisplacementSeriesTendstoOne."
                    + "golden_displacement_series_tendsto_one"),
                H("The displacement series tends to one"),
                StatementSource.FromAuthor(TendstoOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real w, as s tends to positive infinity, the sum of "
                        + "dTerm(s,w) tends to one. No summability hypothesis is required.")),
                    Paragraph(Text(
                        "The terms at indices zero and one are identically zero and one. At "
                        + "every index n at least two, le_nS gives nS(n) at least n, hence "
                        + "strictly greater than one. Its negative-s real power therefore "
                        + "tends to zero, while the n-dependent second factor stays fixed.")),
                    Paragraph(Text(
                        "For the fixed w, set s0=max(0,1-w)+1. Then s0 is nonnegative and "
                        + "s0+w is strictly greater than one, so dTerm_summable gives absolute "
                        + "summability at (s0,w). Term nonnegativity converts this to summability "
                        + "of dTerm(s0,w). Eventually s is at least s0, and the exported termwise "
                        + "parameter-order "
                        + "inequality then bounds the nonnegative term dTerm(s,w,n) by the "
                        + "summable baseline term dTerm(s0,w,n). Mathlib's dominated convergence "
                        + "theorem for infinite sums passes the pointwise limit through the sum.")),
                    Paragraph(Text(
                        "The theorem does not claim a convergence rate, uniformity in w, a "
                        + "joint two-parameter limit, an infimum characterization, or any finite-s "
                        + "evaluation of the series."))),
                DescribeRole.Theorem))));

    private static Formula TendstoOneFormula()
    {
        Formula s = F.Id("s");
        Formula w = F.Id("w");
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));

        return F.Disp(F.Seq(
            F.Forall, F.Sp, w, F.Sp, F.InMacro, F.Sp, reals,
            F.Comma, F.Quad, F.RowBreak,
            F.Lim, F.Underscore, F.Grp(s, F.Sp, F.To, F.Sp, F.Infty), F.Sp,
            Tsum(s, w), F.Sp, F.Eq, F.Sp, F.D(1), F.Dot));
    }

    private static Formula Tsum(Formula s, Formula w)
    {
        Formula n = F.Id("n");
        return F.Seq(
            F.Sum, F.Underscore, F.Grp(n, F.Eq, F.D(0)),
            F.Caret, F.Grp(F.Infty), F.Sp, Call("dTerm", s, w, n));
    }

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
