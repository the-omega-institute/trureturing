using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class WindowCanonicalPrefixesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual prefixes in the extended execution.",
        H("Actual prefixes in the extended execution"),
        Blocks(
            Paragraph(Text("For every split into a prefix and suffix, the very same final accepting execution contains the actual boundary after that prefix. Its state stores the original Horner coordinates and the actual number of windows read, including null padding.")),
            Paragraph(Text("The prefix time is at most the final time and at most four plus the prefix length multiplied by the sum of fifteen times the whole height and forty-six. At that boundary the packed work head is at origin, the source head is at the split, and the saved low bit is the exact prefix seam.")),
            Describe.Lean(DescribeId.Create("source-prefix-registers"), DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalPrefixes.source_prefix_registers"), H("source prefix registers"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: source_prefix_registers (pre suf : List Window) (e : Bool) (T : \u2115) (hg : D5.S3.Arith.ZeckendorfFutureKernel.legal false (NativeContinuation.NullReplyFiber.highBits ((pre ++ suf).map Original.letter))) (hfinal : run (initial (pre++suf) e) T = registerEnd (pre++suf) e) : \u2203 q : \u2115, q \u2264 T \u2227 q \u2264 4+pre.length*(15*(pre++suf).length+46) \u2227 run (initial (pre++suf) e) q = base (boundary (inputSource (pre++suf) e) pre.length (columnsAfter [zeros] pre) 0 (.source (seamAfter false pre))) \u2227 Original.pair (columnsAfter [zeros] pre) = NativeContinuation.JointLaw.composition (pre.map Original.letter) \u2227 valueCount (columnsAfter [zeros] pre) = pre.length \u2227 (columnsAfter [zeros] pre).length \u2264 1+3*pre.length"))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionFidelity"))]));
}
