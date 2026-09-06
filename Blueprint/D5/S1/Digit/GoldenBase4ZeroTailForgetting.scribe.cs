using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class GoldenBase4ZeroTailForgettingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/GoldenBase4ZeroTailForgetting.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Long terminal zero tails have a state-independent arithmetic output. Independent tail channels therefore cannot strengthen the gap-only completion problem.",
        H("Golden Base-Four Long-Tail Output"),
        Blocks(
            Describe.Lean(DescribeId.Create("golden-four-long-tail-digit"),
                DeclarationHandle.Create(Prefix + "longTailDigit"),
                H("The alternating terminal digit"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For tail length at least two, even lengths have digit three and odd lengths digit zero. The function is defined at all lengths, but the machine theorem retains the lower-length guard."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("golden-four-zero-tail-output"),
                DeclarationHandle.Create(Prefix + "zero_tail_output"),
                H("Every transient reference state has the same long-tail output"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two zero steps enter the negative core. Subsequent zero steps alternate between two finite cores. Induction uses the original run semantics and transition table, and covers every tail length."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("golden-four-zero-tail-arithmetic"),
                DeclarationHandle.Create(Prefix + "zero_tail_arithmetic_digit"),
                H("The terminal law agrees with the exact floor difference"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A successful prefix in the previous-one fiber may have arbitrary length. Appending at least two zeroes gives the parity digit under the original Fibonacci valuation, by the existing interval-machine arithmetic theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("golden-four-free-tail-completion"),
                DeclarationHandle.Create(Prefix + "free_tail_completion_iff"),
                H("Free terminal channels carry no additional gap constraint"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary trace, labels and fixed tail-zero/tail-one readouts, all longer parity labels can always be extended by constant readouts. Both directions are proved. This equivalence applies to independent readouts; it does not replace the common-map constraints imposed by an actual finite recurrent carrier."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/GoldenBase4IntervalMachine"))]));
}
