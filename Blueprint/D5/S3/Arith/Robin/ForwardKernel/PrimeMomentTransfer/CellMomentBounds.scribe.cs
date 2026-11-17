using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class CellMomentBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cell sampling bounds connect discrete second and fourth moments with the fixed unit sampling interval.",
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
                    "For N at least two, log N at least one, H and M at least one, and MH at most N, the normalized discrete increments are bounded by 4(M+1)sqrt(H log N) for natural n with floor(N)<=n<=ceil(2N). On [1,2], the continuous increments have the same bound plus (2 log(4N)+2)/sqrt(H log N), uniformly in 0<=a<=b<=M."))),
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
                DescribeId.Create("uniform-cell-second"),
                DeclarationHandle.Create(Prefix + "uniform_cell_second"),
                H("Uniform cell second moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume singular-series values one on the empty set and singletons, MeanSquareHL(3,SS,beta) and the interval correlation input, with 0<alpha<beta<1/3 and M>=1. There is C>=1 such that eventually the second integral of the normalized floor sampled increment on [1,2] is at most C uniformly over natural H between N^alpha and N^beta and all 0<=a<=b<=M. The same cell quadrature estimate applies to second and fourth powers; this second bound uses only the quadratic arithmetic transfer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-cell-fourth"),
                DeclarationHandle.Create(Prefix + "uniform_cell_fourth"),
                H("Uniform cell fourth moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume singular-series values one on the empty set and singletons, MeanSquareHL4(SS,beta) and the interval correlation bounds, with 0<alpha<beta<1/4 and M>=1. There is a constant C>=1 such that, for all sufficiently large N, the fourth integral of the normalized floor sampled increment on [1,2] is at most C, uniformly in natural H between N^alpha and N^beta and 0<=a<=b<=M."))),
                DescribeRole.Theorem))));
}
