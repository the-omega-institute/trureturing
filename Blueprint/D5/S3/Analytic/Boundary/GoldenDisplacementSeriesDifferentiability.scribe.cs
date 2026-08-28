using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class GoldenDisplacementSeriesDifferentiabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden displacement sum is differentiable at every point of its exact "
        + "convergence region.",
        H("Golden Displacement Series Differentiability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-differentiability"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Boundary/GoldenDisplacementSeriesDifferentiability."
                    + "golden_displacement_series_differentiableOn"),
                H("The displacement sum is differentiable on its convergence region"),
                StatementSource.FromAuthor(DifferentiabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At a parameter pair in the convergence region, the two strict affine "
                        + "constraints give a positive margin delta. Lowering both coordinates "
                        + "by twice that margin produces another parameter pair in the region. "
                        + "The term family evaluated at this lower pair is summable.")),
                    Paragraph(Text(
                        "The index-zero term is identically zero and its derivative is the zero "
                        + "map. At every positive index, differentiating the two real-power "
                        + "factors gives two linear-map summands with coefficients containing "
                        + "log(nS(n)) and log(n). The proof uses log(x) <= x^delta/delta and the "
                        + "coordinatewise exponent inequalities on the open quadrant above the "
                        + "intermediate parameter pair. The norm of each derivative summand is "
                        + "bounded by "
                        + "dTerm at the lower pair divided by delta. At index one both logarithms "
                        + "are zero, consistently with dTerm(s,w,1) being constant.")),
                    Paragraph(Text(
                        "Consequently, the sequence whose nth value is "
                        + "(2/delta) times dTerm at the lower parameter pair is summable and "
                        + "bounds the norm of the nth Frechet derivative throughout that open "
                        + "quadrant. Pinned Mathlib's local preconnected-domain theorem for "
                        + "derivatives of infinite sums therefore gives a Frechet derivative at "
                        + "the original parameter pair.")),
                    Paragraph(Text(
                        "The theorem records differentiability only on the exact summability "
                        + "region. It does not publish a formula for the derivative, claim higher "
                        + "smoothness, or assert one derivative majorant valid up to the region's "
                        + "boundary."))),
                DescribeRole.Theorem))));

    private static Formula DifferentiabilityFormula()
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
            "DifferentiableOn",
            real,
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
