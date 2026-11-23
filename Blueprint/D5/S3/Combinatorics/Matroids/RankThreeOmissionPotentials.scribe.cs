using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeOmissionPotentialsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integral joint lifting obstruction of a rank-three sparse-paving matroid with singleton parallel classes.",
        H("Point Potentials and Cyclic Factors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-three-omission-point-potential"),
                DeclarationHandle.Create(Module + ".IsOmissionPotential"),
                H("Normalized point potentials"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A potential vanishes at the chosen anchor, has zero total sum, and is killed by three at every point. "
                    + "It takes equal values at the ends of every pair in no omitted triple. Its values on each omitted triple sum to zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rank-three-obstruction-matrix-kernel"),
                DeclarationHandle.Create(Module + ".rank_three_lifting_obstruction_equiv_kernel"),
                H("Reduced matrix for the integral obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose the bases on a finite ordered ground set of size n greater than three are all triples "
                    + "except a specified family whose distinct members meet in at most one point. "
                    + "For singleton parallel classes and any distinct root and anchor, the integral lifting obstruction "
                    + "is linearly equivalent over the integers to the kernel of the reduced omitted-triangle matrix modulo n. "
                    + "Each column is an increasing pair avoiding the root and anchor. "
                    + "The row of a triple evaluates the alternating form on two differences from the first point of the triple."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-three-obstruction-torsion-count"),
                DeclarationHandle.Create(Module + ".rank_three_lifting_obstruction_torsion_card"),
                H("Torsion count at any divisor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Index the omitted triples without repetition, let m be their number, and choose any anchor. "
                    + "Put b equal to the binomial coefficient counting pairs from n minus two points. For each positive divisor q of n, "
                    + "the number of elements killed by q, multiplied by q to the power m, equals q to the power b times "
                    + "the number of normalized potentials with values modulo the greatest common divisor of q and three. "
                    + "The signed rows identify the transpose kernel with point-potential differences, and the finite character "
                    + "pairing relates the sizes of the primal and transpose kernels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-three-obstruction-cyclic-factors"),
                DeclarationHandle.Create(Module + ".rank_three_lifting_obstruction_cyclic_factors"),
                H("Cyclic factors for all rank-three omission families"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For m distinct omitted triples under the intersection bound, choose any anchor for the potentials. "
                    + "Put b equal to the binomial coefficient counting pairs from n minus two points. The integral lifting obstruction "
                    + "is linearly equivalent over the integers to b minus m cyclic factors of order n and d cyclic factors "
                    + "of order three. The normalized potentials with values modulo the greatest common divisor of n and three "
                    + "number exactly three to the power d. "
                    + "Smith normal form splits the unconstrained residue coordinates from the remaining finite module. "
                    + "The torsion counts at n and its greatest common divisor with three show that this latter module is killed by three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-three-affine-plane-cyclic-factors"),
                DeclarationHandle.Create(Module + ".affine_plane_lifting_obstruction_cyclic_factors"),
                H("Cyclic factors of the twelve affine-line omissions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the nine points of the affine plane of order three, omit its twelve lines and keep all other triples as bases. "
                    + "The normalized potentials are the linear forms in the two affine coordinates. Their two independent "
                    + "slopes give nine potentials. The integral obstruction therefore has nine cyclic factors of order nine "
                    + "and two cyclic factors of order three."))),
                DescribeRole.Theorem))));
}
