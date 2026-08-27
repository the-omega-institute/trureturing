using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class GoldenDisplacementSeriesLogConvexityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithm of the golden displacement sum is convex on its exact convergence region.",
        H("Golden Displacement Series Log-Convexity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-log-convexity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Convexity/GoldenDisplacementSeriesLogConvexity."
                    + "golden_displacement_series_log_convex"),
                H("The displacement sum is log-convex on its convergence region"),
                StatementSource.FromAuthor(LogConvexityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public theorem uses the standard ConvexOn formulation: the domain "
                        + "is exactly the set of parameter pairs for which dTerm is summable, "
                        + "and the function is the real logarithm of the corresponding sum.")),
                    Paragraph(Text(
                        "For positive weights a and b with a+b=1, each mixed dTerm is exactly "
                        + "the product of the endpoint dTerms raised to a and b. At index zero, "
                        + "both positive real powers vanish. At a positive index, n and nS(n) "
                        + "are positive, so Real.mul_rpow, Real.rpow_mul, and Real.rpow_add "
                        + "combine the two endpoint factors without an inequality.")),
                    Paragraph(Text(
                        "The public countable weighted Holder interpolation theorem bounds the "
                        + "mixed sum by the product of the endpoint sums raised to a and b. Its "
                        + "nonnegativity hypotheses come from dTerm_nonneg, and its endpoint "
                        + "summability hypotheses come from the two parameter pairs lying in "
                        + "the convergence region, since dTerm is not summable for arbitrary "
                        + "parameters. This node is the first consumer of the extracted "
                        + "general series inequality.")),
                    Paragraph(Text(
                        "The frozen convexity theorem keeps the mixed parameter pair inside the "
                        + "exact summability region. Every convergent displacement sum is "
                        + "positive because all terms are nonnegative and the term at index one "
                        + "is one. Monotonicity of the real logarithm and its product and "
                        + "real-power identities therefore turn the Holder bound into the "
                        + "weighted additive inequality required by ConvexOn.")),
                    Paragraph(Text(
                        "The theorem does not claim strict log-convexity, an equality "
                        + "characterization, antitonicity in either parameter, convexity of the "
                        + "unlogged sum, convergence or a finite value on the boundary, or any "
                        + "extension outside the exact summability region."))),
                DescribeRole.Theorem))));

    private static Formula LogConvexityFormula()
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
            p, F.Sp, F.Colon, F.Sp, domain, F.Sp, F.Mapsto, F.Sp,
            F.Log, F.Open, series, F.Close);
        Formula convergenceRegion = SetOf(
            p,
            domain,
            Call("Summable", Call("dTerm", first, second)));

        return F.Disp(Call("ConvexOn", real, convergenceRegion, sumFunction));
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
