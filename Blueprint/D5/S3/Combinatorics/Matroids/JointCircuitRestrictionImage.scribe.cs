using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class JointCircuitRestrictionImageDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/JointCircuitRestrictionImage";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact simultaneous integral circuit restriction image for a loopless rank-two dual.",
        H("The joint integral circuit restriction image"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-integral-circuit-restriction"),
                DeclarationHandle.Create(Module + ".exists_topCycle_joint_aggregateRestrict_iff"),
                H("Weighted balance and common congruence characterize the joint image"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let M be a native matroid with ground E in an arbitrary finite linearly "
                        + "ordered carrier V. Assume the dual has rank two and every vertex of E "
                        + "is a dual nonloop. The class labels are the distinct dual closures of "
                        + "singletons in E. For each such label P, let S be its fiber on E and K "
                        + "the complement of S in E. These complements are exactly the circuits of M.")),
                    Paragraph(Text(
                        "At each basis T of the contraction by K, the aggregate sums over a in K "
                        + "the source coefficient on the union of T with the facet K without a. "
                        + "Each term has the boundary deletion sign at a and the shuffle sign for "
                        + "the ordered facet followed by the ordered T. The aggregate is zero off "
                        + "the contraction bases. The generator at P is the augmented simplex "
                        + "boundary on S multiplied by the shuffle sign of K followed by S and "
                        + "by minus one to the power |K| minus one. A singleton fiber contributes "
                        + "an empty-face coordinate.")),
                    Paragraph(Text(
                        "Let y assign integers to the labels. There is one integral augmented top "
                        + "cycle whose aggregate at every P equals y(P) times its signed generator "
                        + "if and only if the sum of |S| times y(P) over all labels is zero, and "
                        + "|E| divides y(P) minus y(Q) for every pair of labels P and Q. Lean "
                        + "permits arbitrary extensions of y outside the finite set of labels.")),
                    Paragraph(Text(
                        "Assign each ground vertex the integer potential of its dual class. "
                        + "Taking the oriented boundary of the weighted ground facets produces "
                        + "a cycle supported on primal bases. Conversely a pivot recovers the "
                        + "potential differences from the faces that omit it, and the boundary "
                        + "equations determine the remaining faces. The zero coefficients on "
                        + "nonbases force the potentials to agree within each dual class.")),
                    Paragraph(Text(
                        "The two insertion identities transport the complementary-pair sign to "
                        + "the stipulated contraction generator. The scalar at P is the total "
                        + "of the vertex potentials minus |E| times the potential of P. Summing "
                        + "over the vertices gives weighted balance, and subtracting two scalars "
                        + "gives divisibility. For the converse, fix a reference class R and use "
                        + "the potential obtained by dividing y(R) minus y(P) by |E|. Weighted "
                        + "balance makes the sum of the vertex potentials equal y(R), giving "
                        + "all requested coefficients from the same cycle.")),
                    Paragraph(Text(
                        "Complementary faces use the sign convention of combinatorial Alexander "
                        + "duality studied by Björner and Tancer (DOI 10.1007/s00454-008-9102-x). "
                        + "The resulting potential formula is the negative complete-graph "
                        + "Laplacian on vertex potentials constant on the classes. Glass and Kaplan "
                        + "discuss the graph Laplacian in Chip-Firing Games and Critical Groups "
                        + "(arXiv:1908.04395). The signed identification with aggregate circuit "
                        + "restriction is proved here."))),
                DescribeRole.Theorem))));
}
