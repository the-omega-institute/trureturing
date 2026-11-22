using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9BoundaryGramDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral Gram identities for boundaries in the signed nine-cube",
        H("The Gram matrix of the signed boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-boundary-gram-reduced"),
                DeclarationHandle.Create(Prefix + "reduced_boundary_factorization"),
                H("Parity-restricted integral Gram and square determinant"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("K"), Transpose("K"), Sp, Eq, Sp, D(9), F.Id("I"), Minus, F.Id("M"), Transpose("M"), Quad, Sp,
                    CallDet(Seq(D(9), F.Id("I"), Minus, F.Id("M"), Transpose("M"))), Sp, Eq, Sp,
                    CallDet(Seq(F.Id("K"), Underscore, F.Id("e"))), Caret, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a vertex set S, a parity b, and a finite row index type with decidable equality. Inject its indices into cube vertices of parity b. For any integer vertex signs of square one, let M and K be the corresponding switched Huang blocks on the opposite-parity columns inside and outside S, respectively.")),
                    Paragraph(Text("Equal-parity entries vanish, so the full row Gram is entirely accounted for by opposite-parity columns. Splitting those columns yields the first equality. For every equivalence e from the row indices to the exterior column indices, K sub e is K with its columns reindexed by e. Its Gram is unchanged by reindexing, and multiplication and transposition of determinants give the second equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-boundary-gram-balanced"),
                DeclarationHandle.Create(Prefix + "balanced_boundary_factorization"),
                H("Unsigned interior of a balanced support"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("K"), Transpose("K"), Sp, Eq, Sp, D(9), F.Id("I"), Minus, F.Id("M"),
                    Transpose("M")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If S is Huang-balanced and the retained rows belong to S, an integer switching sign exists that makes M the ordinary biadjacency on the retained rows and selected opposite-parity columns.")),
                    Paragraph(Text("On S the integer signs agree with the real balance witness. On each edge, the two endpoint signs cancel the original Huang sign, and nonedges have coefficient zero. The exterior block K uses the same switching function, so the determinant identity holds for every reindexing that makes K square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-boundary-gram-cubic"),
                DeclarationHandle.Create(Prefix + "cubic_reduced_boundary_factorization"),
                H("Square integral boundary after two deletions"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Z"), Transpose("Z"), Sp, Eq, Sp, D(9), F.Id("I"), Minus, F.Id("M"), Transpose("M"), Quad, Sp,
                    CallDet(Seq(D(9), F.Id("I"), Minus, F.Id("M"), Transpose("M"))), Sp, Eq, Sp,
                    CallDet(F.Id("Z")), Caret, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let S be a balanced cubic induced subgraph of the nine-cube with 258 vertices. Delete two distinct selected vertices of the same parity. The two parity classes in S both have size 129 by counting the edges from either side. Each cube parity has 256 vertices, leaving 127 exterior columns opposite the 127 retained rows.")),
                    Paragraph(Text("The factor Z uses a bijection from those rows to the opposite-parity exterior columns of the switched Huang matrix. M uses every selected column of the opposite parity and has ordinary unsigned adjacency entries."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-boundary-gram-separated"),
                DeclarationHandle.Create(Prefix + "separated_cubic_boundary_factorization"),
                H("The separated 72- and 186-vertex supports"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Z"), Transpose("Z"), Sp, Eq, Sp, D(9), F.Id("I"), Minus, F.Id("M"), Transpose("M"), Quad, Sp,
                    CallDet(Seq(D(9), F.Id("I"), Minus, F.Id("M"), Transpose("M"))), Sp, Eq, Sp,
                    CallDet(F.Id("Z")), Caret, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take disjoint Huang-balanced cubic induced supports of sizes 72 and 186 with no cube edge between them. Choose one vertex of each support in the same parity and delete those rows. The union is still cubic because its component neighborhoods are unchanged, and the two balance functions give one switching on its disjoint vertex sets.")),
                    Paragraph(Text("The resulting signed exterior factor Z is square of order 127. The unsigned interior matrix M retains all selected columns of the opposite parity."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Downstream application to spanning trees"), Blocks(
                Paragraph(Text("The separated supports arise in Hong, Wu and Xia's Problem 2 on the nine-cube in Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7. The integral boundary argument revisits the previously recorded paper proof for this branch.")),
                Paragraph(Text("Two graph arguments connect the Lean factorization to spanning trees. First, ordering the rows and columns by support makes M block diagonal because there are no cross edges. The Gram defect is then the direct sum of the two reduced two-step Laplacians, one for each support after its row deletion.")),
                Paragraph(Text("Second, in each cubic bipartite support, eliminate the opposite-parity block 3I from the ordinary Laplacian cofactor at the deleted vertex. The two parity classes have equal size before deletion, so the cofactor equals three times the reduced two-step determinant. The matrix-tree theorem identifies that cofactor with the spanning-tree count."))))),
        []));

    private static Formula Transpose(string name) => Seq(F.Id(name), Caret, F.Id("T"));
    private static Formula CallDet(Formula argument) =>
        new Formula.FunctionCall(FormulaIdentifier.Create("det"), [argument]);
}
