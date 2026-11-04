using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalReindexedBirthDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalReindexedBirth.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total decoding and faithful whole birth enumerations", H("Reindexed whole birth enumerations"), Blocks(
            Describe.Lean(DescribeId.Create("decode-code"),
                DeclarationHandle.Create(Owner + "decode_code"), H("Every code decodes to its original tag"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Injectivity of first-reservation coding makes the inverse on its image exact, including ordinary zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordinary-index-decode"),
                DeclarationHandle.Create(Owner + "ordinaryIndex_decode"), H("Colored ordinary indices decode faithfully"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every ordinary label and every ordinal stage, decoding its assigned index returns the same ordinary label. A zero event can carry zero or a hole color, and both decode to ordinary zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("event-read"),
                DeclarationHandle.Create(Owner + "event_read"), H("Every tag reads both enumerations at one label"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every tag and every ordinal stage, the same assigned index returns the original ordinary support or the supplied delayed support, together with the whole signed sequence at the original measure target. Colored ordinary zero events are included at every stage."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("event-index-decode"),
                DeclarationHandle.Create(Owner + "eventIndex_decode"), H("The common index decodes exactly"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At every stage, decoding the common support and measure index returns its original tag, including delayed tags and all colored ordinary zero events."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("event-index-le"),
                DeclarationHandle.Create(Owner + "eventIndex_le"), H("Every valid event index is within its stage"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At a syntactically valid occurrence of a tag, its common support and measure index is at most the occurrence stage."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("event-index-cofinal"),
                DeclarationHandle.Create(Owner + "eventIndex_cofinal"), H("Every label has cofinal valid indexed occurrences"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For each new label and bound, there is a later valid reservation of a tag on the fixed birth row whose common index equals that label. Code-image labels use their original tags; holes and zero use the double reservation coloring of ordinary zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reindexed-whole-birth"),
                DeclarationHandle.Create(Owner + "reindexBirth"), H("A reindexed whole birth pack"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Ordinary tags retain the original support enumeration, while delayed tags receive a supplied support family on the same carrier. Every measure value uses the decoded original target label, which is at most the new label. The original ordinary codes prove both enumerations onto. The support family V and clopen table B remain identical to the given whole birth. Choosing a delayed support as a coordinate pullback and proving its event launch identity are separate requirements."))), DescribeRole.Definition))));
}
