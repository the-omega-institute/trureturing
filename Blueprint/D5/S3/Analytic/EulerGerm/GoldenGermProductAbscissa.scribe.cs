using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermProductAbscissaDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit golden exponent gives a prime-local Euler product whose exact "
        + "absolute-convergence boundary is one over phi squared.",
        H("Golden Germ Product Abscissa"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-germ-product-abscissa"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/EulerGerm/GoldenGermProductAbscissa."
                    + "golden_germ_product_abscissa"),
                H("The golden germ product has its exact abscissa"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The exponent is the canonical golden exponent already used by the "
                        + "Euler-germ family. Its first two positive values isolate the prime "
                        + "term and the faster tail.")),
                    Paragraph(Text(
                        "The convergence equivalence includes divergence at the boundary. "
                        + "Above that boundary the canonical prime-local factors have the "
                        + "displayed infinite product."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula phiSquared = F.Seq(F.Varphi, F.Caret, F.Grp(F.D(2)));
        Formula phiCubed = F.Seq(F.Varphi, F.Caret, F.Grp(F.D(3)));
        Formula inversePhi = F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(F.Varphi));
        Formula threshold = F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(phiSquared));
        Formula betaAtV = Call("o5Beta", F.Id("v"));
        Formula closedForm = F.Seq(
            betaAtV, F.Sp, F.Eq, F.Sp,
            F.Sqrt, F.Grp(F.D(5)), F.Sp, F.Times, F.Sp, F.Id("v"),
            F.Sp, F.Plus, F.Sp, inversePhi,
            F.Sp, F.Minus, F.Sp,
            Call("fract", F.Seq(F.Open, F.Id("v"), F.Plus, F.D(1), F.Close,
                F.Sp, F.Times, F.Sp, F.Varphi)));
        Formula exactBoundary = F.Seq(
            F.Forall, F.Sp, F.Id("sigma"), F.InMacro,
            F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Sp,
            Call("Summable", F.Seq(
                F.Open, F.Id("p"), F.Comma, F.Id("v"), F.Close,
                F.Mapsto, F.Sp,
                F.Id("e"), F.Caret, F.Grp(F.Minus, F.Id("sigma"), F.Sp,
                    F.Times, F.Sp, Call("goldenSpectrum", F.Id("p"), F.Id("v"))))),
            F.Sp, F.Leftrightarrow, F.Sp, threshold, F.Sp, F.Lt, F.Sp, F.Id("sigma"));
        Formula localFactor = F.Seq(
            F.Sum, F.Underscore, F.Grp(F.Id("v"), F.Ge, F.D(0)),
            F.Id("p"), F.Caret,
            F.Grp(F.Minus, F.Id("s"), F.Sp, F.Times, F.Sp, Call("o5Beta", F.Id("v"))));
        Formula product = F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.Sp, F.Text, F.Grp(F.Id("prime"))),
            localFactor);
        Formula hasProduct = F.Seq(
            F.Forall, F.Sp, F.Id("s"), F.InMacro,
            F.Mathbb, F.Grp(F.Id("C")), F.Comma, F.Sp,
            threshold, F.Sp, F.Lt, F.Sp, F.Re, F.Open, F.Id("s"), F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("HasProd", F.Seq(
                F.Id("p"), F.Mapsto, F.Sp, localFactor), product));

        return F.Disp(F.Seq(
            F.Open, F.Forall, F.Sp, F.Id("v"), F.InMacro,
            F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Sp, closedForm, F.Close,
            F.Sp, F.Land, F.Sp,
            Call("o5Beta", F.D(1)), F.Sp, F.Eq, F.Sp, phiSquared,
            F.Sp, F.Land, F.Sp,
            Call("o5Beta", F.D(2)), F.Sp, F.Eq, F.Sp, phiCubed,
            F.Sp, F.Land, F.Sp,
            F.Open, exactBoundary, F.Close,
            F.Sp, F.Land, F.Sp,
            F.Open, hasProduct, F.Close, F.Dot));
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
