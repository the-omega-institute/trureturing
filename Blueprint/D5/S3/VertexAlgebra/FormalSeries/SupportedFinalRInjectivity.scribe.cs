using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedFinalRInjectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/SupportedFinalRInjectivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injectivity of the six-factor multiplier on nested-supported distributions.",
        H("Nested support and cancellation"), Blocks(
            Describe.Lean(DescribeId.Create("nested-support"),
                DeclarationHandle.Create(Prefix + "NestedSupport"),
                H("A separate second-coordinate cutoff on each first-coordinate row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A three-variable distribution has a uniform lower cutoff x>=-U. For each fixed x it has its own lower cutoff y>=-B(x), uniform over z. There is no z lower bound and no common y cutoff over all x."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finalr-injective"),
                DeclarationHandle.Create(Prefix + "finalR_injective"),
                H("Cancellation of the exact six-factor multiplier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Over any commutative complex algebra R, for all nonnegative k,A,C,D, multiplication by x^k y^k (x+y)^k (x+y+z)^A (y+z)^C z^D is injective between nested-supported coefficient distributions. The zero algebra and zero exponents are included.")),
                    Paragraph(Text("The coordinate shifts and their finite sums preserve nested support. Cancellation of x+y uses the uniform x cutoff, while cancellation of y+z uses the current row's y cutoff. Both use supported_positive_reconstruction from SupportedChannelSeries on the corresponding legal bivariate row.")),
                    Paragraph(Text("For x+y+z, strong induction on the nonnegative row index x+U first eliminates the preceding x row. The zero product recurrence then becomes the y+z recurrence on the current row. That row's own y cutoff makes positive reconstruction finite and proves that the entire row vanishes. This couples the row induction to bivariate reconstruction without strengthening the support hypotheses.")),
                    Paragraph(Text("Iterating these cancellations removes each finite power; applying the resulting zero-kernel statement to F-G proves injectivity. This is a formal algebraic statement about distributions. It does not identify a vertex-algebra channel or assert analytic convergence or sewing."))), DescribeRole.Theorem))));
}
