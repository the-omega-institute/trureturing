using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PriorityLattice;

internal sealed class TestartTreeCodeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/testart2026minimal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native increasing-tree parent codes, maximum-label cycle insertion and exact excedance transport.",
        H("Increasing Trees and Cycle Insertion"),
        Blocks(
            Node("ParentCode", "Positive-label parent codes", "Vertex v represents label v+1; its value is the strictly smaller parent label."),
            Node("NativeTree", "Existing unordered native trees", "The source carrier is the existing IntervalForest tree subtype on labels 0 through n. Its single connected component makes the interval condition automatic; no sibling order is stored."),
            Node("splitCode", "Split off the maximum", "Apply the upstream dependent tuple equivalence to separate the largest vertex parent."),
            Node("insertEquiv", "Insert a new maximum", "The upstream option-permutation decomposition is inverted so the new maximum follows its parent. Parent zero creates a singleton cycle."),
            Node("insert_apply", "The actual inserted permutation", "The insertion equivalence is computed by the upstream option swap and option congruence, so it inserts after the selected positive parent and creates a singleton for parent zero.", DescribeRole.Theorem),
            Node("native_parent_code", "Actual native parent incidence", "Decoding a parent code through the existing treeEquivCode gives exactly its stored parent at every positive native vertex. This is an equality of actual parent fields, rather than a cardinality identification.", DescribeRole.Theorem),
            Node("codeEquiv", "Recursive cycle insertion", "Iterate maximum-label insertion over all parent codes, including size zero."),
            Node("nativeEquiv", "Native carrier interface", "Compose the existing treeEquivCode with insertion. The parent-incidence bridge verifies the actual parent field, and the private statistic identifies each positive internal label with a strict excedance position."),
            Node("HasChild", "Positive internal labels", "A positive label is internal exactly when it occurs as a parent value."),
            Node("Internal", "Native incidence", "A native vertex is internal exactly when some vertex has it as parent."),
            Node("reflectPositions", "Position reflection", "Reverse the first n-1 positions and fix the last; for n=1 this is the identity."),
            Node("dual", "The fixed D operation", "Compose position reflection, the supplied permutation, and full value reflection. In positive coordinates this is D(s)(i)=n+1-s(n-i) for i<n and D(s)(n)=n+1-s(n). The private proofs establish involutivity and strict-excedance transport, including fixed points."),
            Node("dual_formula", "Positive-label formula for D", "For every position, reflectPositions sends positive i to n-i when i<n and fixes n. The output positive value is n+1 minus the supplied permutation value at that reflected position. The theorem includes size one and the last position.", DescribeRole.Theorem),
            Node("TreeClass", "The source restricted tree family", "Internal vertex labels are exactly 0 through a-1 in the native tree on 0 through a+b-1. All other labels are leaves."),
            Node("PermClass", "The published strict-excedance family", "Permutations of a+b-1 positive labels have strict excedance positions exactly 1 through b-1. Fixed points are allowed."),
            Node("insertionClassEquiv", "Restricted insertion equivalence", "For every positive a and b, the insertion implementation restricts to an equivalence between the exact native internal-label class and the published permutation class. This equivalence supplies the restricted inverse laws used by TestartTraversal.result. The latter also proves the literal DFS and minimum-first reconstruction specifications of its algorithms.")), []));

    private static DocumentBlock Node(string declaration, string title, string prose, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("testart-code-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
