using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Regularity;

internal sealed class GoldenDisplacementSeriesSecondOrderRegularityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden displacement sum is twice continuously differentiable at every point "
        + "of its exact convergence region.",
        H("Golden Displacement Series Second-Order Regularity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-second-order-regularity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Regularity/GoldenDisplacementSeriesSecondOrderRegularity."
                    + "golden_displacement_series_contDiffOn_two"),
                H("The displacement sum has second-order regularity on its convergence region"),
                StatementSource.FromAuthor(SecondOrderRegularityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At a parameter pair in the convergence region, the two strict affine "
                        + "constraints give a positive margin delta. The proof lowers both "
                        + "coordinates by three times that margin to obtain a new parameter "
                        + "pair. This lower pair is a point, while the family whose nth value is "
                        + "dTerm at that point is summable. The proof works on the open quadrant "
                        + "above the intermediate pair obtained by lowering both coordinates by "
                        + "delta.")),
                    Paragraph(Text(
                        "For a positive index, the term is rewritten as the exponential of a "
                        + "continuous linear functional whose coefficients are -log(nS(n)) and "
                        + "-log(n). Its first derivative is exponential times that functional; "
                        + "its second derivative is the corresponding iterated continuous "
                        + "linear map. At index zero, the term and both displayed derivative "
                        + "families are zero. At index one, nS(1) = 1 and both logarithms vanish, "
                        + "so the first- and second-derivative terms are also zero. Order zero is "
                        + "handled by the identity between the exponential presentation and "
                        + "dTerm, which transfers the original parameter pair's summability to "
                        + "the exponential family and supplies the base-point hypothesis of "
                        + "the first local termwise-differentiation step.")),
                    Paragraph(Text(
                        "On the open quadrant, coordinatewise real-power monotonicity gives "
                        + "non-strict inequalities. Applying log(x) <= x^delta/delta once bounds "
                        + "the norm of the nth first-derivative continuous linear map by "
                        + "(2/delta) times the nth value of the summable corner-term family. "
                        + "Applying it twice and using (a+b)^2 <= 2a^2+2b^2 bounds the norm of "
                        + "the nth second-derivative continuous linear map by (4/delta^2) times "
                        + "that same corner-term family.")),
                    Paragraph(Text(
                        "The local preconnected-domain theorem for derivatives of infinite sums "
                        + "constructs the first two Frechet derivatives. The second-derivative "
                        + "family is continuous term by term, and continuousOn_tsum makes its sum "
                        + "continuous on the quadrant. These facts give ContDiffAt of order two "
                        + "at the original point, hence ContDiffOn of order two on the exact "
                        + "summability region.")),
                    Paragraph(Text(
                        "The theorem does not claim ContDiffOn of top order, ContDiffOn of every "
                        + "finite order, real analyticity, complex analyticity or continuation, "
                        + "or a published Hessian formula. It also does not provide one "
                        + "derivative majorant valid near the convergence-region boundary, and "
                        + "it does not assert strict termwise decrease."))),
                DescribeRole.Theorem))));

    private static Formula SecondOrderRegularityFormula()
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
            F.D(2),
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
