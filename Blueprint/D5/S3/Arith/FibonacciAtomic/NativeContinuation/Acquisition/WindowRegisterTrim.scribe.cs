using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class WindowRegisterTrimDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical trimming and paid rewinds.",
        H("Canonical trimming and paid rewinds"),
        Blocks(
            Paragraph(Text("Starting from a blank target at its origin, the fixed program writes the home marker and copies one actual packed lane. It walks backwards to erase all high zero bits, preserves the highest one when present, and inserts a single zero bit for value zero. An explicit end marker is written.")),
            Paragraph(Text("Both packed and target heads return to their fixed origins by paid unit moves. Each register phase has at most 32 times the sum of the packed length and one, in local actions. It preserves the selected numeric value and every unrelated tape and head throughout its frame.")),
            Describe.Lean(DescribeId.Create("one-register"), DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterTrim.one_register"), H("one register"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: one_register (m : Track \u2192 \u2124 \u2192 Symbol) (h : Track \u2192 \u2124) (j : Lane) (bs : List Bits) (hw : h workTrack=0) (hj : h (target j)=0) (mw : m workTrack=word bs) (mj : m (target j)=fun _=>.blank) : \u2203 T : \u2115, T \u2264 32*(bs.length+1) \u2227 run (entry m h j) T = config m h j bs ((normalized (bs.map (select j))).map Symbol.unit ++ [.window .zero]) 0 0 (.laneDone j) \u2227 (\u2200 n\u2264T, Frame m h j bs bs.length (run (entry m h j) n)) \u2227 Nat.ofDigits 2 ((normalized (bs.map (select j))).map Bool.toNat)=bitValue (select j) bs \u2227 (normalized (bs.map (select j))=[false] \u2228 \u2203 pre, normalized (bs.map (select j))=pre++[true])"))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterCore"))]));
}
