using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class RiemannZetaPositiveRealSignDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Isolation/RiemannZetaPositiveRealSign."
            + "riemannZeta_ofReal_sign";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Riemann zeta is real on the positive real axis away from one, negative "
            + "below one, and positive above one.",
        H("Riemann Zeta on the Positive Real Axis"),
        Blocks(Describe.Lean(
            DescribeId.Create("riemann-zeta-positive-real-sign"),
            DeclarationHandle.Create(Declaration),
            H("Riemann zeta has the expected positive-real sign"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This theorem supplies the variable positive-real zeta sign input in "
                        + "the golden Euler germ extraction ladder of OACTC parts 580 and "
                        + "581. It advances the boundary left open by the point-specific "
                        + "golden auxiliary nonvanishing theorem: every positive real "
                        + "argument other than one is now covered on both sides of one.")),
                Paragraph(Text(
                    "Below one, adjacent odd-even Dirichlet terms are paired. Every real "
                        + "pair is strictly positive, a derivative majorant gives local "
                        + "uniform convergence on positive real part, and the analytic "
                        + "identity principle identifies the paired sum with the eta "
                        + "factor times zeta. The eta factor is negative there, forcing "
                        + "zeta to be real and negative.")),
                Paragraph(Text(
                    "Above one, the positive Dirichlet series gives a positive real part "
                        + "and zero imaginary part directly. The separate public realness "
                        + "lemma records the common conclusion across both intervals.")),
                Paragraph(Text(
                    "The statement is confined to positive real arguments away from the "
                        + "pole at one. It does not establish O-5 or RH, a complex "
                        + "zero-free region, or an all-order extraction claim."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.NarrativeReference.ToDocument(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenAuxiliaryZetaNonzero")),
            DocumentEdge.NarrativeReference.ToDocument(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderRealAxisSign")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("x");
        Formula zeta = Call("riemannZeta", x);
        Formula hypothesis = F.Seq(
            F.D(0), F.Sp, F.Lt, F.Sp, x,
            F.Sp, F.Land, F.Sp,
            x, F.Sp, F.Neq, F.Sp, F.D(1));
        Formula below = F.Seq(
            x, F.Sp, F.Lt, F.Sp, F.D(1),
            F.Sp, F.Land, F.Sp,
            RealPart(zeta), F.Sp, F.Lt, F.Sp, F.D(0));
        Formula above = F.Seq(
            F.D(1), F.Sp, F.Lt, F.Sp, x,
            F.Sp, F.Land, F.Sp,
            F.D(0), F.Sp, F.Lt, F.Sp, RealPart(zeta));
        Formula conclusion = F.Seq(
            ImaginaryPart(zeta), F.Sp, F.Eq, F.Sp, F.D(0),
            F.Sp, F.Land, F.Sp,
            F.Open,
            F.Open, below, F.Close,
            F.Sp, F.Lor, F.Sp,
            F.Open, above, F.Close,
            F.Close);

        return F.Disp(F.Seq(
            F.Forall, F.Sp, x, F.InMacro, F.Sp, RealNumbers(),
            F.Comma, F.Sp,
            F.Open, hypothesis, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            conclusion, F.Dot));
    }

    private static Formula RealPart(Formula value) =>
        F.Seq(F.Re, F.Open, value, F.Close);

    private static Formula ImaginaryPart(Formula value) =>
        Call("Im", value);

    private static Formula RealNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

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
