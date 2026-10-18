using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalFaceSwitchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalFaceSwitch.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed exchange of actual edge coordinates cancels the two determinant counts on every ac-free multiplicity face.",
        H("Complementary configurations on a fixed edge-multiplicity face"),
        Blocks(
            Node("multiplicity", "The two-copy edge total", DescribeRole.Definition,
                "For two Boolean edge states, multiplicity is their sum as natural numbers, taking values zero, one or two."),
            Node("Face", "A nonempty multiplicity face", DescribeRole.Definition,
                "For a reference ordered pair r of edge configurations, Face r q means that every actual edge has the same two-copy multiplicity in q as in r. This represents every nonempty alpha face without imposing a probability or a terminal partition on it."),
            Node("swap", "A fixed coordinate exchange", DescribeRole.Definition,
                "For a set S of actual edge coordinates, swap exchanges the two Boolean configurations at exactly the coordinates in S and retains both values elsewhere."),
            Node("forced", "Edges open in both reference copies", DescribeRole.Definition,
                "For an endpoint map ends and a reference ordered configuration pair r, forced is the actual graph whose open edges are those open in both reference copies."),
            Node("allowed", "Edges available in the face", DescribeRole.Definition,
                "For an endpoint map ends and a reference ordered configuration pair r, allowed is the actual graph whose open edges are those open in at least one reference copy."),
            Node("face_cancel", "Exact cancellation on an ac-free face", DescribeRole.Theorem,
                "For every vertex type V, finite edge type E, actual endpoint map ends:E->V*V, reference ordered pair r, and vertices a,b,c, assume that no pair q in Face r has first configuration with terminal mode ac. The number of ordered pairs in the face with modes (separate,all) equals the number with modes (ab,bc). Terminal labels may coincide. Forced terminal mergers make both counts zero. Otherwise, remove the forced-open component of b from the allowed graph and let A be the component of a. The absence of an ac realization places c outside A. Exchange the two configurations at exactly the edges incident to A. This preserves every edge multiplicity and is an involution. The wired separation theorem shows that the a-b connection swaps copies while the b-c connection remains in its original copy, giving the required mode bijection. Every graph between the forced and allowed graphs is explicitly realized by a configuration in the same face, so the ac-free premise is checked against the actual edge source.")), []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-face-switch-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
