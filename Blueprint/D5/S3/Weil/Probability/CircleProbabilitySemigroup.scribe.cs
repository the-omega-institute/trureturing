using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class CircleProbabilitySemigroupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Probability/CircleProbabilitySemigroup.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circle probability measures, the existing negative-power Fourier moments, and the existing Toeplitz matrices.",
        H("CircleProbabilitySemigroup"),
        Blocks(
            Describe.Lean(DescribeId.Create("circlemoment-mconv"),
                DeclarationHandle.Create(Prefix + "circleMoment_mconv"), H("Convolution multiplies the original Fourier moments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The convolution is the pushforward of the product of the actual Borel measures under circle multiplication. Fubini proves the moment identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("circle-probability-semigroup-of-fourier"),
                DeclarationHandle.Create(Prefix + "circle_probability_semigroup_of_fourier"), H("Construct the entire probability evolution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All positive normalized matrices and multiplicative continuous coefficients construct one weakly continuous family, its identity law and its actual convolution law. Moment uniqueness gives family uniqueness."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exponential-toeplitz-iff-probability-semigroup"),
                DeclarationHandle.Create(Prefix + "exponential_toeplitz_iff_probability_semigroup"), H("Exponential positivity is equivalent to a realized semigroup"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exponent has value zero at the identity. A probability semigroup with precisely the prescribed coefficients is constructed; neither Schoenberg nor an arithmetic Li criterion is assumed as a theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exponential-probability-forces-nonnegative"),
                DeclarationHandle.Create(Prefix + "exponential_probability_forces_nonnegative"), H("A represented exponential cannot have a negative exponent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The modulus of every moment of a probability measure is at most one. The conclusion is necessary and does not assert that pointwise nonnegative exponents suffice for matrix positivity."))), DescribeRole.Theorem))));
}
