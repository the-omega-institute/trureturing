using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class GoldenGermZetaMeromorphicHalfPlaneDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Isolation/GoldenGermZetaMeromorphicHalfPlane."
            + "golden_germ_zeta_meromorphic_half_plane";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden germ zeta is meromorphic above one over phi cubed and has no "
            + "pole away from one over phi squared.",
        H("Golden Germ Zeta Meromorphic Half-Plane"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-zeta-meromorphic-half-plane"),
            DeclarationHandle.Create(Declaration),
            H("Meromorphy and pole exclusion on the half-plane"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let the germ zeta function be the Riemann zeta function at phi "
                        + "squared times s, multiplied by the normalized golden prime "
                        + "product. On the half-plane where the real part of s exceeds "
                        + "one over phi cubed, this function is meromorphic.")),
                Paragraph(Text(
                    "At one over phi squared, GoldenGermZetaSimplePole supplies "
                        + "meromorphy and the exact simple-pole order. At every other "
                        + "point of the half-plane, the Riemann zeta factor avoids its "
                        + "pole and GoldenGermNormalizedFactorRegularity makes the "
                        + "normalized product analytic.")),
                Paragraph(Text(
                    "Thus the germ is analytic at every point in the region except one "
                        + "over phi squared. The nonnegative meromorphic-order conjunct "
                        + "records pointwise that none of those analytic points is a pole.")),
                Paragraph(Text(
                    "STOPPING JUSTIFICATION: this theorem says nothing about the zero "
                        + "set, nothing at or to the left of the line where the real part "
                        + "of s equals one over phi cubed, and does not compute the order "
                        + "at one over phi squared; the upstream simple-pole node does so."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenGermZetaSimplePole")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermNormalizedFactorRegularity")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula germZeta = F.Id("germZeta");
        Formula complex = ComplexNumbers();
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula a = Fraction(F.D(1), phiSquared);
        Formula threshold = Fraction(F.D(1), Power(F.Varphi, F.D(3)));
        Formula scaledS = F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s);
        Formula normalized = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(p, F.Seq(F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)),
            F.Close, F.Sp, F.Times, F.Sp, LocalFactor(s, p));
        Formula germAtS = F.Seq(
            Call("riemannZeta", scaledS), F.Sp, F.Times, F.Sp,
            PrimeProduct(normalized));
        Formula germDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, complex, F.Comma, F.Sp,
            Call("germZeta", s), F.Sp, F.Colon, F.Eq, F.Sp, germAtS);
        Formula region = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, complex, F.Sp, F.Mid, F.Sp,
            threshold, F.Sp, F.Lt, F.Sp,
            F.Re, F.Open, s, F.Close, F.CloseBrace);
        Formula meromorphic = Call("MeromorphicOn", germZeta, region);
        Formula offAbscissa = F.Seq(s, F.Sp, F.Neq, F.Sp, a);
        Formula analyticAway = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, region, F.Comma, F.Sp,
            offAbscissa, F.Sp, F.Rightarrow, F.Sp,
            Call("AnalyticAt", complex, germZeta, s));
        Formula orderAway = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, region, F.Comma, F.Sp,
            offAbscissa, F.Sp, F.Rightarrow, F.Sp,
            F.D(0), F.Sp, F.Leq, F.Sp,
            Call("meromorphicOrderAt", germZeta, s));

        return F.Disp(new Formula.Aligned([
            F.Seq(germZeta, F.Colon, F.Sp, complex, F.Sp, F.To, F.Sp,
                complex, F.Comma),
            F.Seq(germDefinition, F.Comma),
            F.Seq(meromorphic, F.Sp, F.Land),
            F.Seq(F.Open, analyticAway, F.Close, F.Sp, F.Land),
            F.Seq(orderAway, F.Dot),
        ]));
    }

    private static Formula LocalFactor(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

    private static Formula PrimeProduct(Formula body) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.InMacro, F.Sp, Call("Primes", NaturalNumbers())),
            body);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula NaturalNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

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
