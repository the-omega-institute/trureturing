using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class CellMomentBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cell sampling bounds connect discrete fourth moments with the fixed unit sampling interval.",
        H("Cell moment bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-dyadic-probability"),
                DeclarationHandle.Create(Prefix + "unit_dyadic_probability"),
                H("Unit interval probability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lebesgue measure restricted to the interval [1,2] is a probability measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-crude-bounds"),
                DeclarationHandle.Create(Prefix + "normalized_crude_bounds"),
                H("Uniform pointwise bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For N at least two, log N at least one, H and M at least one, and MH at most N, the normalized discrete increments are bounded by 4(M+1)sqrt(H log N). On [1,2], the continuous increments have the same bound plus (2 log(4N)+2)/sqrt(H log N), uniformly in 0<=a<=b<=M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sampling-memlp"),
                DeclarationHandle.Create(Prefix + "sampling_memLp"),
                H("Fourth integrability on one sampling space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same size and endpoint conditions, both t mapped to Z(H,a,b,Nt,N) and t mapped to S(H,a,b,floor(Nt))/sqrt(H log N) belong to L4 for Lebesgue measure restricted to [1,2]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-cell-fourth"),
                DeclarationHandle.Create(Prefix + "uniform_cell_fourth"),
                H("Uniform cell fourth moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume the normalized singular series values, HL4 and the interval correlation bounds, with 0<alpha<beta<1/4 and M>=1. There is a constant C>=1 such that, for all sufficiently large N, the fourth integral of the normalized floor sampled increment on [1,2] is at most C, uniformly in natural H between N^alpha and N^beta and 0<=a<=b<=M."))),
                DescribeRole.Theorem))));
}
