using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy;

internal sealed class CoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact polynomial coefficient provenance.",
        H("Exact polynomial coefficient provenance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coefficients-coefficientpolynomial-surjective"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Coefficients.coefficientPolynomial_surjective"),
                H("Finite coefficient representations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every rational polynomial has a finite ascending coefficient list. Constants use singleton lists, addition uses recursive coefficient addition, and multiplication by X inserts a leading zero. Trailing zeros are allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coefficients-evenized-coefficients-sound"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Coefficients.evenized_coefficients_sound"),
                H("Even polynomial coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Negating alternating coefficients represents substitution of -X. Averaging that list with the original list therefore represents one half of p(X)+p(-X), including the empty list."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coefficients-coefficientsofexpr-sound"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Coefficients.coefficientsOfExpr_sound"),
                H("Expression provenance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If the executable expression parser returns a coefficient list, the corresponding semantic polynomial is exactly coefficientPolynomial of that list. The induction handles constants, the variable, sums, negations, products and squares; inversion is rejected."))),
                DescribeRole.Theorem)),
        []));
}
