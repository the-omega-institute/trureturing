using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class WindowAcquisitionCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Window arithmetic by local actions.",
        H("Window arithmetic by local actions"),
        Blocks(
            Paragraph(Text("Eight tracks have fixed origins. A transition reads one finite symbol, writes one finite symbol, or moves one head by one cell. Work is blank initially. The five input letters encode 000, 100, 010, 101 and 001 with low bit printed first. The source order is high to low and its independent unit letter ends acquisition.")),
            Paragraph(Text("The finite carry updates the two binary Horner coordinates and the binary window count together. The scan writes actual bits, flushes at most three extra columns, tests the home marker and pays for its backward head motion. Safe preserves the source tape, parked source head and unused tapes, and bounds the moving work head throughout the attained run.")),
            Describe.Lean(DescribeId.Create("update-scan-return"), DeclarationHandle.Create("D5/S0/Computability/WindowAcquisitionCore.update_scan_return"), H("update scan return"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: update_scan_return (source : \u2124 \u2192 Symbol) (p : \u2124) (bs : List Bits) (previous : Bool) (carry : Carry) : \u2203 T : \u2115, T \u2264 5 * bs.length + 18 \u2227 run (boundary source p bs 1 (.scan previous carry)) T = boundary source p (updated carry bs) 0 (.sourceMove previous) \u2227 (updated carry bs).length \u2264 bs.length + 3 \u2227 \u2200 t \u2264 T, Safe source p (bs.length + 3) (run (boundary source p bs 1 (.scan previous carry)) t)"))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/Coding/PhysicalSixParser"))]));
}
