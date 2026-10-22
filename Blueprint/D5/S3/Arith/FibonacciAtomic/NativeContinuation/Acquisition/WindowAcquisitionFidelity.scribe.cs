using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class WindowAcquisitionFidelityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Read-only input and exact returned frame.",
        H("Read-only input and exact returned frame"),
        Blocks(
            Paragraph(Text("The input tape is read-only at every time, including after the program halts. At the canonical endpoint its head is at the actual independent unit position. All work heads are at origin. The original packed column stays unchanged.")),
            Paragraph(Text("Unused tracks remain blank. Each normalized register has at most one more bit than the packed column length. The separate registers are a stronger endpoint for arithmetic continuation; a routine requiring another tape convention or a parked input head needs a paid connecting run.")),
            Describe.Lean(DescribeId.Create("run-source"), DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionFidelity.run_source"), H("run source"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: run_source (c : Config) (n : \u2115) : (run c n).cell sourceTrack=c.cell sourceTrack"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("endpoint-frame"), DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionFidelity.endpoint_frame"), H("endpoint frame"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: endpoint_frame (w : List Window) (e : Bool) : (registerEnd w e).cell sourceTrack=inputSource w e \u2227 (registerEnd w e).cell workTrack=word (Original.finalColumns w e) \u2227 (\u2200 t : Track,(\u2200 j : Lane,t \u2260 target j) \u2192 t \u2260 sourceTrack \u2192 t \u2260 workTrack \u2192 (registerEnd w e).cell t=fun _=>.blank) \u2227 (\u2200 t : Track,(registerEnd w e).head t=if t=sourceTrack then w.length else 0) \u2227 (\u2200 j : Lane,(normalized ((Original.finalColumns w e).map (select j))).length \u2264 (Original.finalColumns w e).length+1)"))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalAcquisition"))]));
}
