using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualOccurrenceRightStripHeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal heights in the actual zeta zero enumeration",
        H("Reciprocal heights in the actual zeta zero enumeration"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-right-strip-inverse-height-summable"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualOccurrenceRightStripHeight.actual_rightStrip_inverse_height_summable"),
            H("Use the canonical enumeration with analytic multiplicity"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The fixed-strip zero-density estimate gives summability on distinct zeros weighted by "
                + "their analytic orders. Expanding each finite multiplicity fiber yields the same "
                + "estimate for the actual occurrence indices used by the explicit formula."))),
            DescribeRole.Theorem))));
}
