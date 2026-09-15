using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class InfiniteSuccessorFibresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fibres of the Infinite Digit Successor.",
        H("Fibres of the Infinite Digit Successor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("infinitesuccessorfibres-next-fibres"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/InfiniteSuccessorFibres.next_fibres"),
                H("Surjectivity and all predecessors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first adjacent zero successor preserves the condition that no two adjacent "
                    + "digits are both one, and every legal infinite Boolean sequence has a predecessor. "
                    + "The zero sequence has exactly two predecessors: u has ones at the even positions "
                    + "and v has ones at the odd positions, with positions indexed from zero. Every "
                    + "nonzero sequence has exactly one predecessor. Its first one determines the "
                    + "position of the predecessor's first adjacent zero pair, its lower digits form "
                    + "the unique alternating prefix, ending in one when nonempty, and its higher digits are retained."))),
                DescribeRole.Theorem))));
}
