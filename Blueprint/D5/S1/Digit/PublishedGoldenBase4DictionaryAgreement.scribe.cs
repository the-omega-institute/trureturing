using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PublishedGoldenBase4DictionaryAgreementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pinned 201-record published base-four dictionary agrees with the exact golden-ratio word and digit oracles.",
        H("Published Golden Base-Four Dictionary Agreement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("published-power-records-match-oracle"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/PublishedGoldenBase4DictionaryAgreement.published_power_records_match_oracle"),
                H("All published power records match the exact repository oracle"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source artifact has one distinguished zero row followed by 200 records indexed by powers 4^i. Each compact record stores the output, bit width, and binary value of the most-significant-first input word.")),
                    Paragraph(Text(
                        "A native computation checks every compact row against the computable Zeckendorf word and displacement-based Beatty digit. A separate theorem identifies the displacement computation with the real-floor definition.")),
                    Paragraph(Text(
                        "The transcribed source is pinned to Git blob cebad54295a07797e33a5ce32a5bae51572fafbf, byte length 116101, in aaronbarnoff/tcs_digits."))),
                DescribeRole.Theorem)),
        []));
}
