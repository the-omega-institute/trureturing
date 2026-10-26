using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier.PositiveDefinite;

internal sealed class ClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Fourier/PositiveDefinite/Closure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closure of positive definite translation kernels.",
        H("Positive definite functions"), Blocks(
            Describe.Lean(DescribeId.Create("pd-closure-smul"),
                DeclarationHandle.Create(Prefix + "smul"), H("Nonnegative scalar multiples"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication by a nonnegative real scalar preserves every finite complex Gram inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-closure-sum"),
                DeclarationHandle.Create(Prefix + "sum"), H("Finite sums"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite sum of translation kernels with positive semidefinite Gram matrices again has positive semidefinite Gram matrices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-closure-mul"),
                DeclarationHandle.Create(Prefix + "mul"), H("Pointwise products"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Schur product theorem applies to the two Gram matrices on the same finite point family."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-closure-dilation"),
                DeclarationHandle.Create(Prefix + "dilation"), H("Real dilations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Replacing every point x by a times x proves closure for every real a, including zero and negative values."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-closure-limit"),
                DeclarationHandle.Create(Prefix + "limit"), H("Pointwise limits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed cone of positive semidefinite matrices contains the entrywise limit along every nontrivial filter."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-closure-character"),
                DeclarationHandle.Create(Prefix + "character"), H("Unitary characters"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The character exp(i s t) gives a rank one complex Gram matrix for each real frequency s."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-closure-cos"),
                DeclarationHandle.Create(Prefix + "cos"), H("Cosine kernels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Cosine is the average of the characters with opposite frequencies."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-closure-const"),
                DeclarationHandle.Create(Prefix + "const"), H("Nonnegative constants"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonnegative constant is a nonnegative multiple of the frequency zero character."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-closure-pow"),
                DeclarationHandle.Create(Prefix + "pow"), H("Natural powers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Repeated Schur products prove closure under natural pointwise powers. This assertion does not concern general real powers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-closure-exp"),
                DeclarationHandle.Create(Prefix + "exp"), H("Pointwise exponentials"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exponential series consists of Schur powers with nonnegative factorial coefficients; finite partial sums and pointwise convergence give positivity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-closure-integral"),
                DeclarationHandle.Create(Prefix + "integral"), H("Positive measure integrals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the parameter family is positive definite almost everywhere and each point evaluation is integrable against the positive measure. Conjugation and finite Gram sums commute with the integral; every complex quadratic form remains nonnegative."))), DescribeRole.Theorem))));
}
