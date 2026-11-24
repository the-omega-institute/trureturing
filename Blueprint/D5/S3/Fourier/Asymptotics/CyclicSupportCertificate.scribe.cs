using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicSupportCertificateDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicSupportCertificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A boundary variation and a finite dual certificate control which cyclic weights are strictly positive.",
        H("Sign certificates for cyclic support"),
        Blocks(
            Describe.Lean(DescribeId.Create("outer-activation-variation"),
                DeclarationHandle.Create(Owner + ".boundary_variation_pos"),
                H("Strict positivity at the outer level"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let T be the largest of the sampled levels xᵢ, with at least one smaller level. " +
                    "For a quadratic variation with zero total mass and positive first moment, " +
                    "eliminate the constant and linear coefficients using those two moment equations. " +
                    "The remaining quadratic term at T is proportional to the sum over ordered pairs " +
                    "of (xᵢ−xⱼ)²(T−xᵢ)(T−xⱼ). This is the numerator of the monic orthogonal quadratic " +
                    "in the pair-average formula. Each summand is nonnegative, while the first moment " +
                    "term is strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-cosine-support-certificate"),
                DeclarationHandle.Create(Owner + ".exact_support_of_dual"),
                H("Exact finite support from two excluded levels"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quadratic has nonpositive coefficients of the two cosine deficits. " +
                    "Its values are positive on the candidate set and negative at both endpoints bounding " +
                    "the excluded cosines. Convexity implies strict negativity at every excluded sample. " +
                    "The candidate equals the positive part of the polynomial and has mass one and the " +
                    "two exact moments. The squared distance to this candidate is strictly positive for any " +
                    "distinct competitor, and the clipping and moment slack terms are nonnegative."))),
                DescribeRole.Theorem))));
}
