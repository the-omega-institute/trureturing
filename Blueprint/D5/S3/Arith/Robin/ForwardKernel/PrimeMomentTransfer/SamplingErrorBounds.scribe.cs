using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SamplingErrorBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SamplingErrorBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second and fourth moments control continuous sampling and weighted finite product replacement.",
        H("Sampling error bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-cubic-difference"),
                DeclarationHandle.Create(Prefix + "weighted_cubic_difference"),
                H("Cubic replacement from second moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let f and g be three L2 factors on [1,2], whose cubic products are integrable. Assume every squared integral is at most K and every pointwise difference is at most e>=0. An integrable weight bounded by B>=0 changes the cubic product integral by at most 6 B e K. Expanding the product difference gives three terms, each with a bounded difference factor and two remaining factors. The inequality 2|uv|<=u^2+v^2 controls those two factors with second moments alone; no uniform third or fourth moment bound is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-sampling-second"),
                DeclarationHandle.Create(Prefix + "uniform_sampling_second"),
                H("Uniform second moments and pointwise sampling error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume the singular series equals one on the empty set and singletons, the three-point mean-square hypothesis MeanSquareHL(3,SS,beta), the interval correlation estimates, 0<alpha<beta<1/3 and M>=1. The normalized continuous and floor sampled increments have uniformly bounded squared integrals on [1,2], and their pointwise difference tends uniformly to zero over N^alpha<=H<=N^beta and 0<=a<=b<=M. Each increment is bounded at each individual scale and therefore belongs to L4 for integrability purposes; no uniform fourth integral estimate enters this conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-product-difference"),
                DeclarationHandle.Create(Prefix + "weighted_product_difference"),
                H("Weighted product replacement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On [1,2] with restricted Lebesgue measure, let 1<=k<=4 and let both families belong to L4, with fourth integrals at most K and fourth difference integrals at most D. For an integrable weight of absolute value at most B, the difference of its two product integrals is at most B k D^(1/4) K^((k-1)/4)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-sampling-fourth"),
                DeclarationHandle.Create(Prefix + "uniform_sampling_fourth"),
                H("Uniform continuous and sampled fourth moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume singular-series values one on the empty set and singletons, MeanSquareHL4(SS,beta) and the interval correlation bounds, with 0<alpha<beta<1/4 and M>=1. There is C>=1 such that, for every positive delta and all sufficiently large N, both normalized continuous and floor sampled increments belong to L4 on [1,2], both fourth integrals are at most C, and their fourth difference integral is at most delta^4, uniformly in natural H between N^alpha and N^beta and 0<=a<=b<=M."))),
                DescribeRole.Theorem))));
}
