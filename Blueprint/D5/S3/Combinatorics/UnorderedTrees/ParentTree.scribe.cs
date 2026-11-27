using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class ParentTreeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/UnorderedTrees/ParentTree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite rooted parent trees admit unordered vertex isomorphisms. Their vertex-height and internal-vertex count descend to the finite isomorphism quotient.",
        H("Actual unordered rooted trees"),
        Blocks(
            Node("tree", "Rooted parent trees", "Tree",
                Disp(Call("Tree", F.Id("V"))),
                "A tree consists of a parent map on its original vertices, a distinguished fixed root, and a proof that every vertex reaches that root after finitely many parent steps. The child relation omits the artificial root loop. No order is imposed on any child fiber.",
                DescribeRole.Definition),
            Node("iso", "Actual vertex isomorphisms", "Iso",
                Disp(Call("Iso", F.Id("T"), F.Id("S"))),
                "An isomorphism is a bijection of the complete original vertex carriers that sends the root to the root and commutes with the parent maps. Thus it preserves and reflects every nonroot child edge.",
                DescribeRole.Definition),
            Node("code", "The existing classifier on the whole vertex carrier", "code_eq_iff_iso",
                Disp(Seq(Forall, Sp, F.Id("T"), Comma, Sp, F.Id("S"), Comma, Sp,
                    Call("branchCode", Call("parent", F.Id("T")), Call("root", F.Id("T"))), Eq,
                    Call("branchCode", Call("parent", F.Id("S")), Call("root", F.Id("S"))),
                    Sp, Iff, Sp, Call("Nonempty", Call("Iso", F.Id("T"), F.Id("S"))))),
                "The vertex carriers are arbitrary finite types, independently of one another. A periodic vertex reaching a fixed root must be that root. Consequently transient-child edges are exactly the nonroot parent edges and every original vertex belongs to the root descendant carrier. The existing actual-vertex branch-code classifier therefore applies to the complete vertex sets. Converting its descendant equivalence to a vertex equivalence gives the forward direction; restricting a parent-map isomorphism gives the reverse direction.",
                DescribeRole.Theorem),
            Node("depth-reaches", "The depth iterate reaches the root", "reaches_depth",
                Disp(Seq(Call("iterate", Call("parent", F.Id("T")), Call("depth", F.Id("T"), F.Id("v")), F.Id("v")),
                    Eq, Call("root", F.Id("T")))),
                "For every rooted parent tree and original vertex v, the parent iterate at depth(v) is the root. This is the defining least hitting-time property.", DescribeRole.Theorem),
            Node("depth-minimum", "Minimality of the depth", "depth_le",
                Disp(Seq(Call("iterate", Call("parent", F.Id("T")), F.Id("k"), F.Id("v")),
                    Eq, Call("root", F.Id("T")), Sp, To, Sp,
                    Call("depth", F.Id("T"), F.Id("v")), Sp, Le, Sp, F.Id("k"))),
                "Every iterate reaching the root has index at least the depth of its starting vertex.", DescribeRole.Theorem),
            Node("depth-root", "The root has depth zero", "depth_root",
                Disp(Seq(Call("depth", F.Id("T"), Call("root", F.Id("T"))), Eq, D(0))),
                "The zero iterate already reaches the root when it starts at the root.", DescribeRole.Theorem),
            Node("depth-parent", "The nonroot depth step", "depth_parent",
                Disp(Seq(F.Id("v"), Neq, Call("root", F.Id("T")), Sp, To, Sp,
                    Call("depth", F.Id("T"), F.Id("v")), Eq,
                    Call("depth", F.Id("T"), Call("parent", F.Id("T"), F.Id("v"))), Plus, D(1))),
                "Every nonroot original vertex is exactly one level deeper than its parent. Minimality of the two hitting times gives both inequalities.", DescribeRole.Theorem),
            Node("height", "Vertex-height", "height",
                Disp(Seq(Call("height", F.Id("T")), Eq,
                    D(1), Plus, Call("max", Call("depth", F.Id("T"))))),
                "Depth is the least number of parent steps reaching the root. Vertex-height is one plus its maximum over all original vertices. A nonroot vertex has depth exactly one greater than its parent. Commutation with parent iteration proves depth invariance, and the vertex bijection transports the maximum.",
                DescribeRole.Definition),
            Node("internal", "Internal-vertex count", "internalCount",
                Disp(Call("internalCount", F.Id("T"))),
                "An internal vertex has a nonroot child. The count is the cardinality of this subtype of original vertices. Every actual vertex isomorphism induces a bijection of internal vertices.",
                DescribeRole.Definition),
            Node("classes", "The actual finite quotient", "treeSetoid",
                Disp(Call("TreeClass", F.Id("n"))),
                "For n vertices, take all rooted parent data on Fin n and identify two such data precisely when their branch codes agree. The preceding theorem identifies this equivalence relation with actual unordered rooted vertex isomorphism. The carrier is finite: a datum is determined by its finite parent map and root. Vertex-height and internal-vertex count lift to this quotient by their isomorphism invariance.",
                DescribeRole.Definition),
            Node("count", "The counting sequence", "a",
                Disp(Seq(Call("a", F.Id("n")), Eq,
                    Call("card", Seq(OpenBrace, F.Id("T"), Colon, Sp, Call("TreeClass", F.Id("n")), Sp, Mid, Sp, Seq(
                        Call("classHeight", F.Id("T")), Eq,
                        Call("classInternalCount", F.Id("T"))), CloseBrace)))),
                "The sequence counts the actual size-n unordered rooted-tree classes whose vertex-height equals their internal-vertex count. Its definition uses this finite isomorphism quotient, without a prescribed recurrence or a restricted family of skeletons.",
                DescribeRole.Definition))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("parent-tree-" + id),
            DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
