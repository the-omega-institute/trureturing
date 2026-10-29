using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class OctahedronBlockDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/OctahedronBlock.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimal forts in complete equipartite graphs with two vertices per part.",
        H("Whole parts and transversals"),
        Blocks(
            Node("part", "A whole part", "part", "For any natural m and any i in Fin m, part i is the two-element vertex set consisting of (i,0) and (i,1). The actual graph is Mathlib's completeEquipartiteGraph m 2 on Fin m times Fin 2, with adjacency exactly when first coordinates differ.", DescribeRole.Definition),
            Node("transversal", "A transversal", "Transversal", "For any natural m and any vertex subset S, Transversal S means that the first-coordinate projection is injective on S. It is equivalent to saying that S contains no whole two-vertex part.", DescribeRole.Definition),
            Node("equipartite-minimal", "All minimal forts", "equipartite_minimal_iff", "For every natural m at least two and every actual vertex subset S, S is an inclusion-minimal nonempty fort if and only if S is one whole part, or S has cardinality three and is a transversal. A set of at least three vertices is a fort because an outside vertex has at most one nonneighbor in the set. Whole parts are forts. A transversal fort must have at least three vertices: a two-element transversal leaves a mate with exactly one selected neighbor. Minimality therefore gives exactly the stated two classes, and both classes are minimal. Empty subsets and all proper subsets are included in these arguments.", DescribeRole.Theorem),
            Node("equipartite-rooted", "All choices containing the universal root", "equipartite_rooted_iff", "For every natural m at least two and every base subset S, rootSet S is a minimal fort in the graph with a new universal root if and only if S has cardinality two and is a transversal. The root characterization requires minimal domination and no contained base fort. Fort-freeness excludes whole parts and forces transversality; domination needs two distinct parts, while any such pair dominates and is minimal. Thus these are all rooted choices.", DescribeRole.Theorem),
            Node("equipartite-block", "Unbounded exact counts", "equipartite_block", "For every natural m at least two the actual graph has order 2*m, its full minimal-fort count is m + 8*choose(m,3), its full rooted-choice count is 4*choose(m,2), and every vertex has a neighbor. For arbitrary natural m and k, transversals of size k are in bijection with a k-element subset of Fin m together with a function choosing one of the two vertices in each selected part. Taking first-coordinate support recovers the selected parts, and injectivity recovers each choice. This gives choose(m,k)*2^k transversals. Whole parts are indexed injectively by Fin m and are disjoint from three-element transversals. At m=2 the counts are 2 and 4; at m=3 they are 11 and 12 on six vertices. The latter specialization supplies the octahedral blocks in the mixed graph count.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
