using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SuccessorContinuityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuity of the First Adjacent Zero Successor.",
        H("Continuity of the First Adjacent Zero Successor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("successorcontinuity-infinite-successor-continuous"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/SuccessorContinuity.infinite_successor_continuous"),
                H("Continuity on infinite legal digits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An infinite legal Boolean sequence has no adjacent ones. Its successor erases "
                    + "the digits below the first adjacent zero pair, puts a one at the first position "
                    + "of that pair, and retains the higher digits. A sequence with no adjacent zero "
                    + "pair is sent to the zero sequence. Agreement on the first N plus one input "
                    + "digits forces agreement on the first N output digits: an earlier zero pair "
                    + "has the same first position in both inputs, while the absence of such a pair "
                    + "makes both output prefixes zero. This proves continuity into the ambient "
                    + "product of discrete Boolean spaces, including at both alternating sequences."))),
                DescribeRole.Theorem))));
}
