using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermProductZerosDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden germ product has exactly the prime-2 zeros on its convergence "
            + "half-plane, and any such zeros are isolated.",
        H("Golden Germ Product Zeros"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-germ-product-zeros"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/EulerGerm/GoldenGermProductZeros."
                        + "golden_germ_product_zeros"),
                H("Golden germ zeros localize at prime 2 and are isolated"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The domain inequality points to the right: the real part is "
                            + "strictly greater than one over phi squared. At every point "
                            + "of this open half-plane, the full prime product is nonzero "
                            + "exactly when the explicit prime-2 scalar series is nonzero.")),
                    Paragraph(Text(
                        "The theorem exhibits s = 1 inside the half-plane with nonzero "
                            + "product. Thus the domain is nonempty and the analytic product "
                            + "is not identically zero before the identity theorem is used.")),
                    Paragraph(Text(
                        "Every point in the half-plane has a punctured ambient neighborhood "
                            + "free of product zeros and prime-2 local-factor zeros. The "
                            + "known unconditional region has real part greater "
                            + "than or equal to two thirds. Whether any zero exists in the "
                            + "strip where one over phi squared is strictly less than the "
                            + "real part and the real part is strictly less than two thirds "
                            + "remains open."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula one = F.D(1);
        Formula two = F.D(2);
        Formula threshold = Fraction(one, Power(F.Varphi, two));
        Formula productAtOne = PrimeProduct(one);
        Formula s = F.Id("s");
        Formula z = F.Id("z");
        Formula productAtS = PrimeProduct(s);
        Formula factorTwoAtS = LocalFactor(s, two);

        Formula witness = F.Seq(
            threshold, F.Sp, F.Lt, F.Sp, RealPart(one),
            F.Sp, F.Land, F.Sp,
            productAtOne, F.Sp, F.Neq, F.Sp, F.D(0));
        Formula localization = ForallComplex(s, F.Seq(
            threshold, F.Sp, F.Lt, F.Sp, RealPart(s),
            F.Sp, F.Rightarrow, F.Sp,
            F.Open, productAtS, F.Sp, F.Neq, F.Sp, F.D(0),
            F.Sp, F.Leftrightarrow, F.Sp,
            factorTwoAtS, F.Sp, F.Neq, F.Sp, F.D(0), F.Close));
        Formula productIsolation = ForallComplex(z, F.Seq(
            threshold, F.Sp, F.Lt, F.Sp, RealPart(z),
            F.Sp, F.Rightarrow, F.Sp,
            EventuallyNonzero(z, PrimeProduct(F.Id("w")))));
        Formula factorIsolation = ForallComplex(z, F.Seq(
            threshold, F.Sp, F.Lt, F.Sp, RealPart(z),
            F.Sp, F.Rightarrow, F.Sp,
            EventuallyNonzero(z, LocalFactor(F.Id("w"), two))));

        return F.Disp(new Formula.Aligned([
            F.Seq(witness, F.Sp, F.Land),
            F.Seq(F.Open, localization, F.Close, F.Sp, F.Land),
            F.Seq(F.Open, productIsolation, F.Close, F.Sp, F.Land),
            F.Seq(F.Open, factorIsolation, F.Close, F.Dot),
        ]));
    }

    private static Formula ForallComplex(Formula variable, Formula body) =>
        F.Seq(
            F.Forall, F.Sp, variable, F.InMacro, F.Sp, ComplexNumbers(),
            F.Comma, F.Sp, body);

    private static Formula EventuallyNonzero(Formula center, Formula value) =>
        Call("Eventually", F.Seq(
            F.Id("w"), F.Sp, F.Mapsto, F.Sp,
            value, F.Sp, F.Neq, F.Sp, F.D(0)), Call("nhdsNE", center));

    private static Formula LocalFactor(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

    private static Formula PrimeProduct(Formula s) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.InMacro, F.Sp, Call("Primes", NaturalNumbers())),
            LocalFactor(s, F.Id("p")));

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula RealPart(Formula value) =>
        F.Seq(F.Re, F.Open, value, F.Close);

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
