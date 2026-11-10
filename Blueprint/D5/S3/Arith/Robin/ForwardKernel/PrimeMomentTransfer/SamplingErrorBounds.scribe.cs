using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SamplingErrorBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SamplingErrorBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth moments control continuous sampling and weighted finite product replacement.",
        H("Sampling error bounds"),
        Blocks(
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
                    "Assume the normalized singular series values, HL4 and the interval correlation bounds, with 0<alpha<beta<1/4 and M>=1. There is C>=1 such that, for every positive delta and all sufficiently large N, both normalized continuous and floor sampled increments belong to L4 on [1,2], both fourth integrals are at most C, and their fourth difference integral is at most delta^4, uniformly in natural H between N^alpha and N^beta and 0<=a<=b<=M."))),
                DescribeRole.Theorem))));
}
