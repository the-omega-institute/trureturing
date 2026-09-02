using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GermProductNonvanishingAboveThreeFifthsDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/EulerGerm/GermProductNonvanishingAboveThreeFifths.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime-2 golden local factor and the full golden Euler product are "
            + "nonzero when the real part is at least three fifths.",
        H("Golden Germ Nonvanishing Above Three Fifths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-two-germ-nonvanishing-above-three-fifths"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "germ_local_factor_two_ne_zero_of_re_ge_three_fifths"),
                H("The prime-2 local factor is nonzero above three fifths"),
                StatementSource.FromAuthor(PrimeTwoFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This is the prime-2 step in the golden Euler-germ extraction "
                            + "ladder of OACTC Parts 580 and 581, on the RH-route O-5 "
                            + "control line. It advances the explicit prime-2 "
                            + "nonvanishing boundary from real part two thirds to real "
                            + "part three fifths.")),
                    Paragraph(Text(
                        "At the new endpoint, exact rational power bounds give the first "
                            + "tail coefficient below seventeen fiftieths and the "
                            + "geometric ratio below thirty-three fiftieths. Their sum is "
                            + "strictly below one, so the excited tail cannot cancel the "
                            + "vacuum term.")),
                    Paragraph(Text(
                        "The remaining strip between one over phi squared and three "
                            + "fifths is not decided. The statement neither asserts a "
                            + "local zero below three fifths nor proves O-5 or the Riemann "
                            + "hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-germ-product-nonvanishing-above-three-fifths"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "germ_product_ne_zero_of_re_ge_three_fifths"),
                H("The full golden Euler product is nonzero above three fifths"),
                StatementSource.FromAuthor(ProductFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Odd-prime local factors were already nonzero throughout the open "
                            + "convergence half-plane. Combining that frozen result with "
                            + "the improved prime-2 estimate makes every local factor "
                            + "nonzero when the real part is at least three fifths.")),
                    Paragraph(Text(
                        "The frozen summability bridge then supplies the nonzero t-product. "
                            + "The separately frozen convergence theorem carries the "
                            + "Multipliable assertion on this half-plane; the notation for "
                            + "the t-product alone is not being used as an existence claim.")),
                    Paragraph(Text(
                        "This consequence advances one nonvanishing boundary in the "
                            + "OACTC 580/581 extraction ladder. It does not close the lower "
                            + "convergence strip, locate any germ zero, or imply the O-5 "
                            + "control statement or RH."))),
                DescribeRole.Theorem))));

    private static Formula PrimeTwoFormula()
    {
        Formula s = F.Id("s");
        return F.Disp(ForallComplex(s, F.Seq(
            HalfPlaneCondition(s), F.Sp, F.Rightarrow, F.Sp,
            LocalFactor(s, F.D(2)), F.Sp, F.Neq, F.Sp, F.D(0), F.Dot)));
    }

    private static Formula ProductFormula()
    {
        Formula s = F.Id("s");
        return F.Disp(ForallComplex(s, F.Seq(
            HalfPlaneCondition(s), F.Sp, F.Rightarrow, F.Sp,
            PrimeProduct(s), F.Sp, F.Neq, F.Sp, F.D(0), F.Dot)));
    }

    private static Formula HalfPlaneCondition(Formula s) =>
        F.Seq(
            Fraction(F.D(3), F.D(5)), F.Sp, F.Le, F.Sp,
            RealPart(s));

    private static Formula ForallComplex(Formula variable, Formula body) =>
        F.Seq(
            F.Forall, F.Sp, variable, F.InMacro, F.Sp, ComplexNumbers(),
            F.Comma, F.Sp, body);

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
