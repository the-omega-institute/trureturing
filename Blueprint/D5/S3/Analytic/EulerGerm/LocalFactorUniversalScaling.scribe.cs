using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class LocalFactorUniversalScalingDocument
    : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden prime-local factors are logarithmic rescalings of one universal series, "
            + "and their second normalized deviations are absolutely summable down to "
            + "the strict lower edge one over twice phi cubed.",
        H("Golden Local-Factor Universal Scaling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("germ-local-factor-prime-scaling"),
                DeclarationHandle.Create(Module + "germLocalFactor_prime_scaling"),
                H("Prime-local factors are logarithmic rescalings"),
                StatementSource.FromAuthor(PrimeScalingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive prime bases, the principal complex power is the "
                            + "exponential of the exponent times the real logarithm. "
                            + "After multiplying the argument by log p over log q, every "
                            + "term of the q-local series equals the matching p-local "
                            + "term.")),
                    Paragraph(Text(
                        "The identity asserts only universal scaling. It does not assert "
                            + "that any local factor has a zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("germ-local-factor-next-mode-expansion"),
                DeclarationHandle.Create(
                    Module + "germLocalFactor_next_mode_expansion"),
                H("The normalized local factor exposes its next mode and exact tail"),
                StatementSource.FromAuthor(NextModeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first four exponent values are zero, phi squared, phi "
                            + "cubed, and phi to the fourth. Since phi to the fourth is "
                            + "phi squared plus phi cubed, those four terms factor as "
                            + "one plus x times one plus y.")),
                    Paragraph(Text(
                        "For positive real part, the norm of x is strictly below one, so "
                            + "the displayed inverse is legitimate. The remaining sum "
                            + "starts exactly at o5Beta of four."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "second-normalized-factor-deviation-norm-summable-sharp"),
                DeclarationHandle.Create(
                    Module
                        + "second_normalized_factor_deviation_norm_summable_sharp"),
                H("The second normalized deviations are summable at the sharp edge"),
                StatementSource.FromAuthor(SharpSummabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The leading deviation is the square of the phi-cubed mode. Its "
                            + "prime sum converges precisely under the strict inequality "
                            + "two times phi cubed times the real part of s greater than "
                            + "one; the tail is controlled from o5Beta of four onward.")),
                    Paragraph(Text(
                        "This sharpens the frozen sufficient bound one over phi to the "
                            + "fourth to the golden-window lower edge one over twice phi "
                            + "cubed. It asserts no zero of any local factor."))),
                DescribeRole.Theorem)),
        []));

    private static Formula PrimeScalingFormula()
    {
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula s = F.Id("s");
        Formula logarithmicRatio = Fraction(Call("log", p), Call("log", q));
        Formula scaled = F.Seq(
            logarithmicRatio, F.Sp, F.Times, F.Sp, s);
        Formula equality = Equal(
            LocalFactor(s, p),
            LocalFactor(scaled, q));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("p", Primes()),
                Bound("q", Primes()),
                Bound("s", ComplexNumbers()),
            ],
            equality));
    }

    private static Formula NextModeFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula x = GoldenMode(p, s, 2);
        Formula y = GoldenMode(p, s, 3);
        Formula oneMinusY = Parenthesize(
            F.Seq(F.D(1), F.Sp, F.Minus, F.Sp, y));
        Formula inverseOnePlusX = Power(
            Parenthesize(F.Seq(F.D(1), F.Sp, F.Plus, F.Sp, x)),
            F.Seq(F.Minus, F.D(1)));
        Formula normalizer = F.Seq(
            oneMinusY, F.Sp, F.Times, F.Sp,
            inverseOnePlusX, F.Sp, F.Times, F.Sp);
        Formula left = F.Seq(
            normalizer, LocalFactor(s, p),
            F.Sp, F.Minus, F.Sp, F.D(1));
        Formula right = F.Seq(
            F.Minus, Power(Parenthesize(y), F.D(2)),
            F.Sp, F.Plus, F.Sp,
            normalizer, FourthTail(s, p));
        Formula hypothesis = LessThan(F.D(0), RealPart(s));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers()), Bound("p", Primes())],
            Implies(hypothesis, Equal(left, right))));
    }

    private static Formula SharpSummabilityFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula x = GoldenMode(p, s, 2);
        Formula y = GoldenMode(p, s, 3);
        Formula inverseOnePlusX = Power(
            Parenthesize(F.Seq(F.D(1), F.Sp, F.Plus, F.Sp, x)),
            F.Seq(F.Minus, F.D(1)));
        Formula deviation = F.Seq(
            Parenthesize(F.Seq(F.D(1), F.Sp, F.Minus, F.Sp, y)),
            F.Sp, F.Times, F.Sp, inverseOnePlusX,
            F.Sp, F.Times, F.Sp, LocalFactor(s, p),
            F.Sp, F.Minus, F.Sp, F.D(1));
        Formula threshold = Fraction(
            F.D(1),
            F.Seq(
                F.D(2), F.Sp, F.Times, F.Sp,
                Power(F.Varphi, F.D(3))));
        Formula hypothesis = LessThan(threshold, RealPart(s));
        Formula summable = Call(
            "Summable",
            F.Seq(
                p, F.Colon, F.Sp, Primes(),
                F.Sp, F.Mapsto, F.Sp,
                new Formula.Norm(deviation)));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers())],
            Implies(hypothesis, summable)));
    }

    private static Formula FourthTail(Formula s, Formula p)
    {
        Formula k = F.Id("k");
        Formula index = F.Seq(k, F.Sp, F.Plus, F.Sp, F.D(4));
        Formula exponent = F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp,
            Call("o5Beta", index));

        return F.Seq(
            F.Sum, F.Underscore,
            F.Grp(k, F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, exponent));
    }

    private static Formula GoldenMode(
        Formula p,
        Formula s,
        int exponent) =>
        Power(p, F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp,
            Power(F.Varphi, F.D((byte)exponent))));

    private static Formula LocalFactor(Formula s, Formula p) =>
        Call("germLocalFactor", s, p);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula RealPart(Formula value) =>
        F.Seq(F.Re, F.Open, value, F.Close);

    private static Formula Parenthesize(Formula value) =>
        F.Seq(F.Open, value, F.Close);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Primes() =>
        Call("Primes", NaturalNumbers());

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula NaturalNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
