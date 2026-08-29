using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class GaugeStableZeroDefectDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/GaugeStableZeroDefect."
            + "gauge_preserves_completion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gauge-invariant normalization and defect data preserve completion status.",
        H("Gauge-Stable Zero Defect"),
        Blocks(Describe.Lean(
            DescribeId.Create("gauge-stable-zero-defect"),
            DeclarationHandle.Create(Declaration),
            H("Gauge-Stable Zero Defect"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Completion combines a normalization target with a zero-defect condition.")),
                Paragraph(Text(
                    "Any gauge transport preserving both values preserves membership in the completed locus in both directions."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("gauge_invariant_normalization_and_defect"), Sp, Rightarrow, Sp,
            F.Id("completion_status_invariant"), Dot));
}
