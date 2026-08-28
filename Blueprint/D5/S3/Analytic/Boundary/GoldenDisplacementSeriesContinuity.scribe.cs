using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class GoldenDisplacementSeriesContinuityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden displacement sum is continuous at every point of its exact convergence "
        + "region.",
        H("Golden Displacement Series Continuity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-continuity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Boundary/GoldenDisplacementSeriesContinuity."
                    + "golden_displacement_series_continuousOn"),
                H("The displacement sum is continuous on its convergence region"),
                StatementSource.FromAuthor(ContinuityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At a convergent parameter pair, the two strict affine constraints leave "
                            + "room to lower both coordinates while remaining in the convergence "
                            + "region. The series evaluated at the lowered corner is summable, and its "
                            + "terms provide a majorant.")),
                    Paragraph(Text(
                        "The zero-index term vanishes identically. For every positive index both "
                            + "natural bases are at least one, so increasing either parameter "
                            + "does not increase its real-power factor. On the coordinatewise up-set "
                            + "from that corner the corner series therefore dominates every term "
                            + "uniformly on this neighborhood.")),
                    Paragraph(Text(
                        "Pinned Mathlib's continuousOn_tsum applies on that local up-set. Since the "
                            + "original parameter lies in its interior, the resulting local "
                            + "continuity gives continuity at the chosen point, and hence "
                            + "continuity on the whole convergence region. No majorant uniform over "
                            + "the entire region is asserted."))),
                DescribeRole.Theorem))));

    private static Formula ContinuityFormula()
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

        return F.Disp(Call("ContinuousOn", sumFunction, convergenceRegion));
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
