using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.PartialTransposeSaturation;

internal sealed class PartialTransposeDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/wangchen2025partialtranspose");

    private static DocumentBlock Desc(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite extraction of right and left singular pencil summands",
        H("Two-sided finite pencil reduction"), Blocks(
            Paragraph(Text("A finite pencil is a pair of linear maps between finite-dimensional vector spaces over a field. Repeatedly split off a shortest polynomial right-kernel chain. Each step supplies actual commuting projections and lowers the remaining source dimension. Apply the same construction to the dual of the right-reduced remainder to extract left singular blocks. The final pair has no polynomial kernel chain on either side and has equal source and target dimensions.")),
            Paragraph(Text("The reduction constructs the singular direct summands internally. It does not assume a Kronecker canonical form or the existence of an invertible linear combination for the final square pair. Polynomial regularity of that square pair is a separate statement. The degree zero blocks remain present as common zero rows or columns.")),
            Desc("Pencil", "A finite-dimensional two-arrow pencil",
                "The data consists of finite-dimensional source and target vector spaces over the field and two linear arrows between them. The source and target may both have dimension zero.", DescribeRole.Definition),
            Desc("dual", "Duality reverses both arrows",
                "Replace the source by the dual of the target, the target by the dual of the source, and each arrow by its linear dual. No complex conjugation is involved.", DescribeRole.Definition),
            Desc("RightReduced", "Absence of polynomial right-kernel chains",
                "Every finite coefficient chain satisfying all pencil boundary equations has zero final coefficient. Repeated removal of trailing zeros makes this equivalent to the absence of any nonzero polynomial right-kernel vector.", DescribeRole.Definition),
            Desc("SplitData", "An actual shortest-chain summand",
                "A chain of index r is accompanied by its nonzero endpoint, boundary equations, independent source and image chains, and projections onto their spans. Both arrows intertwine the two projections.", DescribeRole.Definition),
            Desc("remainder", "The simultaneous complementary pencil",
                "Restrict the arrows to the kernels of the source and target chain projections. Their commuting identities ensure both restrictions map into the target kernel.", DescribeRole.Definition),
            Desc("RightReduction", "A finite right singular reduction tree",
                "A leaf is right-reduced. An internal node consists of an actual right-chain split and a reduction of its simultaneous complement.", DescribeRole.Definition),
            Desc("LeftReduction", "Left extraction after right reduction",
                "Each stage remains right-reduced. A leaf is right-reduced on both sides and square. An internal node extracts a right chain from the dual, corresponding to a left singular block in the original pencil.", DescribeRole.Definition),
            Desc("TwoSidedReduction", "A finite two-sided singular reduction tree",
                "Right singular splits precede a finite left reduction. Every split uses actual complementary maps, and each final pair is square with no polynomial kernel chain on either side.", DescribeRole.Definition),
            Desc("two_sided_reduction", "Every finite pencil admits two-sided extraction",
                "First obtain the finite right reduction. At each right-reduced leaf apply the finite left reduction. The resulting tree decomposes the pair into right and left singular chain summands and square two-sided reduced remainders."),
            Desc("tensorRank", "Rank of the two-term tensor map",
                "For two finite complex pencils p and q, take the image dimension of p.first tensor q.first plus p.second tensor q.second. The tensor factor order is fixed throughout.", DescribeRole.Definition),
            Desc("horizontalRank", "Rank of the horizontal pair map",
                "The image dimension of the linear map from two copies of the source that sends (x,y) to first(x)+second(y).", DescribeRole.Definition),
            Desc("verticalRank", "Rank of the joint output map",
                "The image dimension of the map sending x to the ordered pair (first(x),second(x)).", DescribeRole.Definition),
            Desc("horizontalRank_dual", "Duality exchanges horizontal and vertical ranks",
                "The horizontal rank of the dual pencil equals the vertical rank of the original pencil. The dual of the joint output map is the horizontal pair map after the natural product-dual equivalence."),
            Desc("verticalRank_dual", "The other pair-rank duality identity",
                "The vertical rank of the dual pencil equals the original horizontal rank. Restriction of functionals to the two product inclusions identifies the relevant dual map."),
            Desc("horizontalRank_matrix", "Coordinates recover horizontal concatenation rank",
                "In any finite source and target bases, the abstract horizontal pair rank equals the matrix rank of the horizontal concatenation of the two arrow matrices."),
            Desc("verticalRank_matrix", "Coordinates recover vertical concatenation rank",
                "In any finite source and target bases, the abstract joint output rank equals the matrix rank of the vertical concatenation of the two arrow matrices."),
            Desc("tensorRank_matrix", "Arbitrary bases compute tensor rank",
                "Choose finite bases independently in both source and both target spaces. The abstract tensor rank equals the rank of the two-term Kronecker sum of the four arrow matrices."),
            Desc("tensorRank_dual_dual_left", "A first-factor bidual preserves tensor rank",
                "Dualize the first pencil twice. In the two dual bases its arrow matrices are the double transposes of the original arrow matrices, so every tensor rank is unchanged."),
            Desc("tensorRank_comm", "Exchange of tensor factors preserves rank",
                "Exchanging both pencils permutes the product row and column indices. Commutativity of complex scalar multiplication gives equality of tensor ranks."),
            Desc("tensorRank_dual_dual", "Simultaneous duality transposes the full tensor matrix",
                "Dualizing both pencils once transposes their complete tensor matrix in dual bases. Full matrix transposition preserves rank."),
            Desc("tensorRank_dual_left_exchange", "Partial duality moves between the factors",
                "The tensor rank of the dual first pencil with the unchanged second pencil equals that of the unchanged first pencil with the dual second pencil. Combine simultaneous duality with the bidual identity."))));
}
