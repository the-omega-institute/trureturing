using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class WindowAcquisitionPackedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original positive numeral acquisition.",
        H("Original positive numeral acquisition"),
        Blocks(
            Paragraph(Text("The exact positive numeral is acquired from one legal input alone. The actual h counts all supplied windows; no separate height, number or word width enters the initial configuration. The empty window list with unit one is included.")),
            Paragraph(Text("One accepting execution retains the Horner column sum, padding-inclusive counter and exact numeral. The maximum coordinate starts at zero, grows by at most five times the previous maximum plus two, and is at most (five to the h minus one) divided by two. The numeral is strictly below the Fibonacci number at index 3h+3. Time and every historical-space charge belong to this same execution.")),
            Describe.Lean(DescribeId.Create("original-accepting-packed-resources"), DeclarationHandle.Create("D5/S0/Computability/WindowAcquisitionPacked.original_accepting_packed_resources"), H("original accepting packed resources"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: original_accepting_packed_resources : Function.Injective (finiteCode (\u03b1 := Symbol)) \u2227 \u2203 A B : \u2115, 0 < A \u2227 0 < B \u2227 \u2200 (w : List Window) (e : Bool), D5.S3.Arith.ZeckendorfFutureKernel.legal false (NativeContinuation.NullReplyFiber.highBits (w.map letter) ++ [e]) \u2192 0 < numeral w e \u2192 \u2203 T : \u2115, T \u2264 A*(w.length+1)^2 \u2227 run (initial w e) T = boundary (inputSource w e) w.length (finalColumns w e) 0 .done \u2227 program (run (initial w e) T).control = .halt \u2227 pair (finalColumns w e) = NativeContinuation.JointLaw.composition (w.map letter) \u2227 valueCount (finalColumns w e) = w.length \u2227 valueN (finalColumns w e) = numeral w e \u2227 pair (finalColumns w e) = columnSum w \u2227 maximumColumn [] = 0 \u2227 (\u2200 b, maximumColumn (w ++ [b]) \u2264 5*maximumColumn w+2) \u2227 2*maximumColumn w+1 \u2264 5^w.length \u2227 maximumColumn w \u2264 (5^w.length-1)/2 \u2227 valueN (finalColumns w e) < Nat.fib (3*w.length+3) \u2227 (finalColumns w e).length \u2264 3*w.length+4 \u2227 (\u2200 n \u2264 T, chargedBits w e n \u2264 B*(w.length+1)) \u2227 (\u2200 n \u2264 T, Frame (inputSource w e) w.length (3*w.length+5) (run (initial w e) n))"))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/WindowAcquisitionTerminal"))]));
}
