using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Champions;

internal sealed class DecimalBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var t = Id("t");
        var a = Id("a");
        var rTribonacci = Id("rTribonacci");
        var rZeckendorf = Id("rZeckendorf");
        var tolerance = new Formula.Fraction(Num(1), Num(2000000));

        Formula RoundingBound(Formula exactValue, Formula roundedValue) =>
            new Formula.Relation(
                new Formula.Absolute(Subtract(exactValue, roundedValue)),
                FormulaRelationOperator.LessThan,
                tolerance);

        var tribonacciConstantBound = RoundingBound(
            t,
            new Formula.Fraction(Num(1839287), Num(1000000)));
        var shiftedCoefficientBound = RoundingBound(
            Multiply(a, t),
            new Formula.Fraction(Num(618420), Num(1000000)));
        var zeckendorfFingerprintBound = RoundingBound(
            rZeckendorf,
            new Formula.Fraction(Num(1170820), Num(1000000)));
        var tribonacciFingerprintBound = RoundingBound(
            rTribonacci,
            new Formula.Fraction(Num(2092100), Num(1000000)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Four exact frozen constants certify the six-place decimals quoted by the source.",
            H("Certified Decimal Bounds"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("tribonacci-constant-rounding-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/DecimalBounds."
                        + "tribonacci_constant_rounding_bound"),
                    H("Tribonacci Perron-root decimal"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(tribonacciConstantBound)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The characteristic polynomial is negative at 1.8392865 and positive "
                            + "at 1.8392875. The intermediate root is the frozen Perron root "
                            + "by its exact uniqueness theorem, certifying 1.839287."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-shifted-binet-coefficient-rounding-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/DecimalBounds."
                        + "tribonacci_shifted_binet_coefficient_rounding_bound"),
                    H("Shifted Tribonacci Binet-coefficient decimal"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(shiftedCoefficientBound)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Here a times t is exactly the source normalization a prime, as fixed "
                            + "by the normalization bridge. Rational endpoint comparisons "
                            + "certify the decimal 0.618420."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("zeckendorf-coding-fingerprint-rounding-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/DecimalBounds."
                        + "zeckendorf_coding_fingerprint_rounding_bound"),
                    H("Zeckendorf coding-fingerprint decimal"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(zeckendorfFingerprintBound)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The frozen exact value phi squared over square root five, together "
                            + "with exact rational square bounds for square root five, certifies "
                            + "the decimal 1.170820."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-coding-fingerprint-rounding-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/DecimalBounds."
                        + "tribonacci_coding_fingerprint_rounding_bound"),
                    H("Tribonacci coding-fingerprint decimal"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(tribonacciFingerprintBound)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The normalization bridge reduces the fingerprint to a rational "
                            + "function of t. A tighter cubic sign bracket from 1.83928675 to "
                            + "1.83928676 certifies the decimal 2.092100."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Champions/CodingFingerprint")),
            ]));
    }
}
