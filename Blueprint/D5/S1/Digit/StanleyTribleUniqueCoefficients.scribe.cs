using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class StanleyTribleUniqueCoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique coefficients in Stanley's ternary products satisfy a cubic recurrence.",
        H("Stanley's Ternary Unique Coefficients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stanley-weights"),
                DeclarationHandle.Create("D5/S1/Digit/StanleyTribleUniqueCoefficients.G"),
                H("The weight sequence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The weights start at one and three. Each subsequent weight is twice "
                    + "the sum of the two preceding weights."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ternary-product"),
                DeclarationHandle.Create("D5/S1/Digit/StanleyTribleUniqueCoefficients.product"),
                H("The polynomial in the question"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every index below n, the product contains the factor whose three "
                    + "monomials have exponents zero, the weight, and twice the weight. "
                    + "The coefficient semiring is the natural numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unique-coefficient-count"),
                DeclarationHandle.Create("D5/S1/Digit/StanleyTribleUniqueCoefficients.c"),
                H("Count coefficients equal to one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Filter the actual polynomial support by coefficient equal to one "
                    + "and take its cardinality. The definition is not a surrogate "
                    + "sequence specified by the desired recurrence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coefficient-bridge"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/StanleyTribleUniqueCoefficients.multiplicity_eq_coeff"),
                H("Translated multiplicities are polynomial coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Appending a digit adds three translated coefficient functions. "
                    + "Induction, using Mathlib's coefficient formula for multiplication "
                    + "by a power of X, identifies this recursion with the product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-support"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/StanleyTribleUniqueCoefficients.multiplicity_pos"),
                H("The support has no holes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplicity is positive exactly between zero and the span, "
                    + "inclusive. The span is twice the sum of the preceding weights. "
                    + "It is strictly smaller than the next weight and than twice "
                    + "the current weight, so three translated supports never meet."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-overlap"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/StanleyTribleUniqueCoefficients.span_overlap"),
                H("The overlap is two levels shorter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The span two levels later equals the corresponding weight plus "
                    + "the original span. Thus the overlap-prefix count at that later "
                    + "level reduces to the surviving lower part of the original level."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("initial-zero"),
                DeclarationHandle.Create("D5/S1/Digit/StanleyTribleUniqueCoefficients.c_zero"),
                H("The empty product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is exactly one coefficient equal to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("initial-one"),
                DeclarationHandle.Create("D5/S1/Digit/StanleyTribleUniqueCoefficients.c_one"),
                H("One factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There are exactly three coefficients equal to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("initial-two"),
                DeclarationHandle.Create("D5/S1/Digit/StanleyTribleUniqueCoefficients.c_two"),
                H("Two factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There are exactly nine coefficients equal to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-index-recurrence"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/StanleyTribleUniqueCoefficients.c_recurrence"),
                H("Stanley's recurrence for every natural index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The count at n plus three, the count at n plus one, and the count "
                    + "at n sum to three times the count at n plus two. The proof tracks "
                    + "the total count and the unique coefficients in the overlap prefix. "
                    + "Positivity kills uniqueness on each overlap; reflection pairs "
                    + "the outer intervals. The total at the next level plus four times "
                    + "the overlap-prefix count equals three times the current total. "
                    + "The overlap-prefix counts two levels apart sum to the current "
                    + "total. Eliminating these auxiliary counts proves the recurrence, "
                    + "without bounding or classifying the larger multiplicities."))),
                DescribeRole.Theorem))));
}
