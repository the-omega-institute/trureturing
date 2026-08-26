using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermZetaContinuationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/EulerGerm/GoldenGermZetaContinuation."
            + "golden_germ_zeta_continuation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zeta-normalized product canonically continues the golden germ to its larger "
            + "half-plane and remains positive on the real ray.",
        H("Golden Germ Zeta Continuation"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-zeta-continuation"),
            DeclarationHandle.Create(Declaration),
            H("The normalized product gives the unique larger-half-plane continuation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The continued function is quantified on the full normalized-product "
                        + "half-plane rather than defined as the desired factorization.")),
                Paragraph(Text(
                    "The frozen factorization proves that this function agrees with the "
                        + "canonical germ prime product on its original convergence domain. "
                        + "The displayed computation rule then determines it uniquely on the "
                        + "larger half-plane.")),
                Paragraph(Text(
                    "The same frozen estimates supply absolute convergence of the normalized "
                        + "prime factors and positivity on the real ray. The source's numerical "
                        + "window certificate is an empirical remark outside the named theorem."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermZetaFactorization")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula sigma = F.Id("sigma");
        Formula p = F.Id("p");
        Formula continuation = F.Id("Zqc");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula thresholdSquared = Fraction(F.D(1), phiSquared);
        Formula thresholdCubed = Fraction(F.D(1), Power(F.Varphi, F.D(3)));
        Formula local = LocalFactor(s, p);
        Formula normalized = NormalizedFactor(s, p, local, phiSquared);
        Formula germProduct = PrimeProduct(local);
        Formula gAtS = Call("G", s);
        Formula gType = F.Seq(
            F.Id("G"), F.Colon, F.Sp, ComplexNumbers(),
            F.Sp, F.To, F.Sp, ComplexNumbers());
        Formula gDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            gAtS, F.Sp, F.Colon, F.Eq, F.Sp, PrimeProduct(normalized));
        Formula continuationDomain = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, ComplexNumbers(), F.Sp, F.Mid, F.Sp,
            thresholdCubed, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.CloseBrace);
        Formula agreement = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdSquared, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("Zqc", s), F.Sp, F.Eq, F.Sp, germProduct);
        Formula factorization = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdCubed, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("Zqc", s), F.Sp, F.Eq, F.Sp,
            Call("riemannZeta", F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s)),
            F.Sp, F.Times, F.Sp, gAtS);
        Formula absoluteConvergence = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            thresholdCubed, F.Sp, F.Lt, F.Sp, F.Re, F.Open, s, F.Close,
            F.Sp, F.Rightarrow, F.Sp,
            Call("Summable", F.Seq(
                p, F.Colon, F.Sp, Call("Primes", NaturalNumbers()), F.Sp,
                F.Mapsto, F.Sp, F.Lvert, F.Sp,
                normalized, F.Sp, F.Minus, F.Sp, F.D(1), F.Sp, F.Rvert)));
        Formula gAtSigma = Call("G", sigma);
        Formula positivity = F.Seq(
            F.Forall, F.Sp, sigma, F.InMacro, F.Sp, RealNumbers(), F.Comma, F.Sp,
            thresholdCubed, F.Sp, F.Lt, F.Sp, sigma,
            F.Sp, F.Rightarrow, F.Sp,
            F.D(0), F.Sp, F.Lt, F.Sp, F.Re, F.Open, gAtSigma, F.Close,
            F.Sp, F.Land, F.Sp,
            Call("Im", gAtSigma), F.Sp, F.Eq, F.Sp, F.D(0));

        return F.Disp(new Formula.Aligned([
            F.Seq(gType, F.Comma),
            F.Seq(gDefinition, F.Comma),
            F.Seq(
                F.Open, F.Exists, F.Bang, F.Sp, continuation, F.Colon, F.Sp,
                continuationDomain, F.Sp, F.To, F.Sp, ComplexNumbers(), F.Comma),
            F.Seq(F.Open, agreement, F.Close, F.Sp, F.Land, F.Sp,
                F.Open, factorization, F.Close, F.Close, F.Sp, F.Land),
            F.Seq(F.Open, absoluteConvergence, F.Close, F.Sp, F.Land, F.Sp,
                F.Open, positivity, F.Close, F.Dot),
        ]));
    }

    private static Formula LocalFactor(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

    private static Formula NormalizedFactor(
        Formula s,
        Formula p,
        Formula local,
        Formula phiSquared) =>
        F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared)),
            F.Close, F.Sp, F.Times, F.Sp, local);

    private static Formula PrimeProduct(Formula body) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.InMacro, F.Sp, Call("Primes", NaturalNumbers())),
            body);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula RealNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

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
