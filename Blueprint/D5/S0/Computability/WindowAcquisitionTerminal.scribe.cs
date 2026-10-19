using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class WindowAcquisitionTerminalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paid terminal arithmetic and persistent storage.",
        H("Paid terminal arithmetic and persistent storage"),
        Blocks(
            Paragraph(Text("Terminal arithmetic scans the packed column to form twice the first coordinate plus three times the second plus the independent unit. Carry propagation, source-unit reading, zero testing and the return to origin are local actions.")),
            Paragraph(Text("Visited storage includes the supplied input, all origins and the union of every earlier head position, including cells erased or left blank. Charge also counts a fixed finite symbol code, the complete fixed control program, current control and descriptions of every head. The all-prefix frame bounds historical visits in a common interval.")),
            Describe.Lean(DescribeId.Create("scan-return"), DeclarationHandle.Create("D5/S0/Computability/WindowAcquisitionTerminal.scan_return"), H("scan return"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: scan_return (source : \u2124 \u2192 Symbol) (p : \u2124) (bs : List Bits) (carry : Fin 5) (seen : Bool) : \u2203 T : \u2115, T \u2264 5 * bs.length + 18 \u2227 run (boundary source p bs 1 (.finishScan carry seen)) T = boundary source p (finished carry bs) 0 (if seen || hasN (finished carry bs) then .done else .reject) \u2227 (finished carry bs).length \u2264 bs.length + 3 \u2227 \u2200 t \u2264 T, Safe source p (bs.length + 3) (run (boundary source p bs 1 (.finishScan carry seen)) t)"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prefix-charged-bound"), DeclarationHandle.Create("D5/S0/Computability/WindowAcquisitionTerminal.prefix_charged_bound"), H("prefix charged bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: prefix_charged_bound (w : List Window) (e : Bool) (T : \u2115) (hf : \u2200 n \u2264 T, Frame (inputSource w e) w.length (3*w.length+5) (run (initial w e) n)) : \u2200 n \u2264 T, chargedBits w e n \u2264 (programCode.length + Fintype.card Control + 64*(Fintype.card Symbol+1)) * (w.length+1)"))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/WindowAcquisitionPrefixes"))]));
}
