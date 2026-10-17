using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition;

internal sealed class NativeBoundedPreorderControlDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite binary path determines the complete pending preorder frontier.",
        H("Compressed preorder control"), Blocks(
            Paragraph(Text("A source is a nonempty finite ordered full binary tree with Boolean leaves. An address is a finite Boolean list, with false for left and true for right. Reports retain their addresses and four-valued replies in chronological order.")),
            Entry("rightsPending", "Pending right siblings", "For each left edge in p, take the prefix before that edge and append a right edge. List these addresses from the deepest such edge to the shallowest. The list describes the unvisited siblings mathematically; it is not a field of the cursor.", DescribeRole.Definition),
            Entry("nextPath", "Advance after a closed node", "Search for the last left edge of p. If it exists, replace it by a right edge and delete all subsequent edges. Otherwise return none. The recursion examines only p.", DescribeRole.Definition),
            Entry("pending", "The frontier represented by a cursor", "The cursor none represents the empty frontier. A cursor some(p) represents p followed by rightsPending(p).", DescribeRole.Definition),
            Entry("cursorStep", "One structural step", "A branch reply at p moves to p followed by a left edge. Every other reply moves to nextPath(p). Actual source traversal has no absent replies; handling absent as an error is a separate instruction rule.", DescribeRole.Definition),
            Entry("CursorRun", "Path-selected report sequences", "The empty sequence leaves its cursor unchanged. A nonempty sequence at some(p) must first report p, and its remaining reports start at cursorStep(p,r). The relation has no hidden tree, pending-subtree stack, or acquired history in its transition rule.", DescribeRole.Definition),
            Entry("ActualCursorPrefix", "Actual finite prefixes", "The initial cursor is some(empty address), with no reports. A cursor at p reads the actual source at p and advances by cursorStep. Histories label this relation and are not selector arguments.", DescribeRole.Definition),
            Entry("reachable_compressed_frontier_and_trial_simulation", "Exact actual preorder and compressed frontier", "For every source u, the complete acquisitionTrace([],u) is a CursorRun from some(empty address) to none. For every cursor c and history h reached by ActualCursorPrefix(u,c,h), h is a prefix of that complete trace, its existing acquisition frontier equals pending(c), and it is a CursorRun from the initial cursor to c. Further, for every decomposition of the complete trace as h followed by report a and suffix s, h is a CursorRun ending at some(a.address), its frontier is exactly a.address followed by rightsPending(a.address), and s is a CursorRun from cursorStep(a.address,a.reply) to none.", DescribeRole.Theorem),
            Paragraph(Text("The key address identity says that pending(nextPath(p)) is exactly rightsPending(p). Appending a left edge exposes its sibling before all earlier pending siblings. Thus a path step agrees with the independently defined acquisitionStep for every reply. The established actual acquisition execution then supplies the complete path-selected sequence. Induction on actual reads retains a suffix of that sequence, so every actual prefix has the same next query and the same pending queue.")),
            Entry("Mode", "Seven instruction modes", "The modes, in order, are VALUE, GUARD, POLL, UPDATE, HALT0, HALT1 and ERROR.", DescribeRole.Definition),
            Entry("Control", "Intermediate fields", "A control retains only its finite address p, its length s, the branch and leaf counts b and l, candidate index j, parity bit a, and mode mu. No source description or report history is a field.", DescribeRole.Definition),
            Entry("Parameters", "Installed constants", "One controller fixes the positive source size h, starting offset start, last candidate index last, polling literal depth pollDepth and whether the active polling modes are available.", DescribeRole.Definition),
            Entry("canonical", "Canonical exceptional controls", "A canonical control sets every field except the specified mode to zero or the empty address.", DescribeRole.Definition),
            Entry("fresh", "Fresh trial", "A fresh trial has root VALUE mode, the specified candidate index j, and zero length, counters and parity.", DescribeRole.Definition),
            Entry("queryMode", "Mode before a node query", "At offset zero or at the root, begin in VALUE. Otherwise begin in GUARD.", DescribeRole.Definition),
            Entry("Valid", "Field conditions", "Normal controls require s equal to the path length, s and b less than h, l at most h and j at most last. GUARD additionally requires positive offset and a nonempty path. POLL and UPDATE must be canonical and active. Halt and error controls must be canonical.", DescribeRole.Definition),
            Entry("virtualDelta", "Virtual node successors", "A virtual absent reply selects canonical ERROR. A branch reaching the h-th branch resets the trial and increments j if another candidate is available. Other branches descend left only within the path and branch bounds. A leaf increments l and updates parity; nextPath selects the next query. At the end, exactly l+1=h and b=h-1 select canonical HALT with the new parity bit. A saturated leaf counter or any failed condition selects ERROR.", DescribeRole.Definition),
            Entry("controlProgram", "Total source primitive rows", "VALUE reads p followed by halfCeil(start+j) right edges and applies decodeLabel followed by virtualDelta. GUARD reads the parent followed by floor((start+j)/2)+1 right edges; acceptance changes only its mode. POLL reads the installed right-ray literal: absent selects UPDATE, alpha starts candidate zero, and the other replies select ERROR. UPDATE performs one genuine update and returns to POLL. The two canonical halt modes halt; invalid controls and ERROR read the root and select canonical ERROR.", DescribeRole.Definition),
            Paragraph(Text("The proved prefix correspondence concerns the structural cursor and actual traversal order. The definitions also specify the bounded counter and decoder rows. Correct execution of these bounded rows, candidate iteration, a bit-field representation and a physical installed execution require additional operational statements."))
        )));

    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("nativeboundedpreordercontrol-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
