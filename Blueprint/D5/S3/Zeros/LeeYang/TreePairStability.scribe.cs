using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class TreePairStabilityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fiolmartinezmontoyariosfukelman2020quiver");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical Cayley substitution excludes zeros in the disk.", H("The physical Cayley substitution excludes zeros in the disk."),
        Blocks(Paragraph(Text("The complexification is bilinear, with no conjugates. The graph identity retains the leaf constraint t_v=2z/3 and the exact 13/48 compensation per leaf. The internal degree-2 remainder is 5/16. These are identities and inequalities for unbounded finite index types, not tests of particular trees. The real parts of the physical Cayley variables are positive. Leaves obey eta_v=z in real and imaginary parts. The positive real quadratic value, the real sum-of-squares certificate and the bilinear lemma imply nonvanishing for every complex X of norm less than one; independent arbitrary leaf weights are outside this statement.")),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-rank-one-minus-squares-nonzero"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairStability.rank_one_minus_squares_nonzero"),
                H("Rank one minus squares nonzero"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-graph-sum-of-squares"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairStability.graph_sum_of_squares"),
                H("Graph sum of squares"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-pairQuadratic-rank-one"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairStability.pairQuadratic_rank_one"),
                H("Pairquadratic rank one"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiol-arbitrary-tree-physical-pairQuadratic-nonzero"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/TreePairStability.physical_pairQuadratic_nonzero"),
                H("Physical pairquadratic nonzero"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact hypotheses and conclusion are displayed above."))), DescribeRole.Theorem))));
}
