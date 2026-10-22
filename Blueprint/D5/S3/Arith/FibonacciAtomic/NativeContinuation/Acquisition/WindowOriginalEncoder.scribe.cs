using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class WindowOriginalEncoderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent original padded input encoder.",
        H("Independent original padded input encoder"),
        Blocks(
            Paragraph(Text("The original canonical occupied indices are Mathlib Zeckendorf indices, starting at F2=1. The independent unit is occupancy of index two. Window j groups indices 3j+3, 3j+4 and 3j+5 in low-to-high print order. W lists these windows from high to low. A finite renaming alone connects those five letters to the operational alphabet.")),
            Paragraph(Text("L is (the canonical dense word length plus one) divided by three using natural division; the independent unit is excluded from the windows. For every h at least L, W includes exactly h actual windows and retains every leading null. Its expanded high-to-low bit list with the final unit is exactly the padded canonical dense display. The existing canonical-language and numeric-value theorems supply legality and exact number; no length, legality or numeric identity is a new input premise.")),
            Describe.Lean(DescribeId.Create("original-bits"), DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowOriginalEncoder.original_bits"), H("original bits"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: original_bits (h N : \u2115) : NativeContinuation.NullReplyFiber.highBits (W h N) ++ [bit N 0] = display N (3*h+1)"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("padded-windows"), DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowOriginalEncoder.padded_windows"), H("padded windows"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: padded_windows (N h : \u2115) (hh : L N \u2264 h) : W h N = List.replicate (h-L N) .zero ++ W (L N) N"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("local-source"), DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowOriginalEncoder.local_source"), H("local source"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: local_source (h N : \u2115) (hh : L N \u2264 h) : (localWord h N).length=h \u2227 legal false (NativeContinuation.NullReplyFiber.highBits ((localWord h N).map Original.letter) ++ [bit N 0]) \u2227 Original.numeral (localWord h N) (bit N 0)=N"))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionPacked")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/GoldenBase4DenseInput")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/GoldenZeckendorfLanguage"))]));
}
