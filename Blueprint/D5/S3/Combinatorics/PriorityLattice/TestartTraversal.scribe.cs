using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PriorityLattice;

internal sealed class TestartTraversalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PriorityLattice/TestartTraversal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/testart2026minimal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed native increasing-tree and strict-excedance permutation maps, with their operational certificates.",
        H("Decreasing-Child DFS and Minimum-First Cycles"),
        Blocks(
            Node("splice", "Insert a new maximum", "Insert a letter immediately after the selected parent in a distinct-label word. A missing parent leaves the word unchanged."),
            Node("children", "Decreasing native children", "Enumerate child labels in strictly decreasing order. Parent codes are read through the existing native parent-field interface."),
            Node("preorder", "Literal root-first DFS", "Read the root, then recursively read each child subtree in decreasing child-root order. The result theorem proves this defining recursion for the insertion implementation."),
            Node("componentWords", "Delete root zero", "Read the preorder of each child component of the removed zero root. No planar or binary structure is stored or assumed."),
            Node("cycleProduct", "Keep each cyclic direction", "Use the pinned List.formPerm on every component word and multiply the disjoint cycles. Singleton words remain present and give fixed points."),
            Node("CycleWords", "Certified actual cycle words", "The flattened words permute exactly labels 1 through n. Every word starts at its unique minimum. Every actual permutation value equals the next letter, with the final letter returning to the first, by the upstream directed-cycle successor theorem."),
            Node("previousSmaller", "Last smaller entry", "Scan the preceding letters from left to right, replacing the accumulator whenever a letter is strictly smaller than the queried letter. Zero is the initial sentinel."),
            Node("wordParent", "Rightmost preceding smaller letter", "Stop strictly before the queried letter and select the final smaller entry. For a minimum-first cycle its first entry receives zero."),
            Node("parentLookup", "Select the containing cycle", "Use the unique cycle word containing the queried positive label and apply wordParent. The cycle partition prevents conflicting containing words."),
            Node("reconstructCode", "All parent attachments", "Perform the prescribed attachment at every positive label. Every selected parent is strictly smaller, so the code belongs to the existing unrestricted parent-code family."),
            Node("permutationWords", "Minimum-first directed decomposition", "Compute words by inverse maximum insertion. The CycleWords certificate independently checks that these are actual minimum-first cycles of the supplied permutation in its original direction, including all singleton cycles."),
            Node("reconstructTree", "Restore the native root", "Decode all rightmost-smaller attachments through the existing treeEquivCode, retaining the actual native parent fields and root zero."),
            Node("RightmostSmaller", "Exact last-entry certificate", "Either no preceding letter is smaller and the parent is zero, or the prefix splits at the selected smaller parent and every later preceding letter is at least the query."),
            Node("F", "The fixed forward map", "Delete zero, traverse each component root first with decreasing child roots, turn each word into a cycle in that direction, and apply D. The definition uses insertion for execution; ForwardSpec certifies exactly these operations."),
            Node("H", "The fixed inverse map", "Apply D, take its certified minimum-first cycles without reversing their direction, attach every later letter to the rightmost preceding smaller letter, and attach each cycle minimum to restored zero."),
            Node("ForwardSpec", "Native forward specification", "Child membership is equivalent to actual native parent incidence. Child order strictly decreases; preorder satisfies the root-first DFS equation. The component words partition all positive labels and give the actual directed cycles. The reflected position and complemented value formulas are the sealed D formulas."),
            Node("ReverseSpec", "Native inverse specification", "The supplied words are actual minimum-first directed cycles of D. Every reconstructed native parent equals the cycle lookup and satisfies the explicit rightmost-smaller certificate. The restored root has no parent."),
            Node("result", "The full fixed-map theorem",
                "For all positive integers a,b, set n=a+b-1. The source consists of all unordered increasing trees on labels 0 through n with root zero, internal labels exactly 0 through a-1, and leaves exactly a through n. The target consists of all actual permutations of labels 1 through n whose strict excedance positions are exactly 1 through b-1; fixed points are allowed. F and H satisfy their literal operational specifications, F lands in the target, H lands in the source, H(F(t))=t for every source tree, and F(H(s))=s for every target permutation. There is no bound on n, no planar or binary restriction, and no omitted a=1, b=1 or n=1 case.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("testart-2026-question-one-type-c-tree-bijection"),
                    ResolutionKind.Proved)),
            Paragraph(Text("The proof inserts the current maximum immediately after its parent, or as a singleton cycle when its parent is zero. Induction proves that this insertion has the literal decreasing-child DFS recursion, the exact directed cycle successor relation, and the rightmost-smaller parent reconstruction. The individual-label statistic identifies every positive internal vertex with a strict excedance position. The fixed involution D exchanges the required prefix statistics, yielding both restricted landings and inverse identities.")),
            Paragraph(Text("Testart, arXiv:2602.12130v2, Sections 6 and 7 Question 1, supplies the source family and question. Bényi and Hajnal, arXiv:1602.08684v1, Section 3.2 Theorem 12(ii), supplies the published interpretation of the target by C(a,b-1). The count interpretation is attributed to that paper; it is not a newly formalized counting theorem here. The construction answers the tree side of the source disjunction at the mathematical level. No priority claim is made here."))), []));

    private static DocumentBlock Node(string declaration, string title, string prose,
        DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("testart-traversal-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);
}
