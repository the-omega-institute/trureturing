using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy;

internal sealed class UnitLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive unit translation-energy lower bound.",
        H("A positive unit translation-energy lower bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitlowerbound-unit-literal-translationenergy-lower"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/UnitLowerBound.unit_literal_translationEnergy_lower"),
                H("A fixed separated interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The unit literal test has R=1 and p=q=1. For every real shift s between 5/8 and 1, its full translation energy is at least 1/16. A fixed interval in the plateau is separated from a translated cutoff of height at most one half, giving a positive integral contribution."))),
                DescribeRole.Theorem)),
        []));
}
