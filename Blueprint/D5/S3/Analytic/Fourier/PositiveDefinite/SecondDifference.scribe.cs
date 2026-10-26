using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier.PositiveDefinite;

internal sealed class SecondDifferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Fourier/PositiveDefinite/SecondDifference.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive definite functions and their integral representations.",
        H("SecondDifference"), Blocks(
            Describe.Lean(DescribeId.Create("pd-seconddifference-difference"),
                DeclarationHandle.Create(Prefix + "difference"), H("Translation differences"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any complex positive definite function and any real step h, the centered expression 2 f(t) minus f(t+h) minus f(t-h) is positive definite. A doubled finite family and the coefficient map with blocks I and minus I give the Gram congruence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-seconddifference-neg-second-deriv"),
                DeclarationHandle.Create(Prefix + "neg_second_deriv"), H("Negative curvature"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real twice continuously differentiable positive definite function, the negative second derivative is positive definite. The centered differences divided by the squared step converge pointwise by two applications of the derivative quotient limit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-seconddifference-q-integral"),
                DeclarationHandle.Create(Prefix + "Q_integral"), H("Quadratic deficit integral"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an even twice continuously differentiable real function g, its deficit divided by t squared, with value minus one half of its second derivative at zero, equals the integral from zero to one of (1-u) times the negative second derivative at ut. The fundamental theorem applied to (1-u)t g prime(ut) plus g(ut) gives the identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-seconddifference-q-positivedefinite"),
                DeclarationHandle.Create(Prefix + "Q_positiveDefinite"), H("Positive quadratic deficit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If g is even, twice continuously differentiable and positive definite, then its continuously extended quadratic deficit is positive definite. Negative curvature, arbitrary real dilation and the nonnegative weighted integral give the result."))), DescribeRole.Theorem))));
}
