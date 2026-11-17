using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative;

internal sealed class ResonantUniversalInsertionEndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repetition closure for the strict resonant insertion",
        H("Natural repetition and take closure"),
        Blocks(
            Describe.Lean(DescribeId.Create("resonant-repetition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionEndpoint.resonant_target_word_repeated_strict"),
                H("Every finite repetition preserves both target strips"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The strict adaptive lift is closed under every finite repetition and every natural take: each coordinate remains in its target interval and both repeated totals are zero. This is the period closure used by the physical Circle endpoint."))),
                DescribeRole.Theorem)), []));
}
