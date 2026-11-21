using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class RightStripInverseHeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal heights from dyadic zero counts",
        H("Reciprocal heights from dyadic zero counts"),
        Blocks(Describe.Lean(
            DescribeId.Create("summable-right-strip-inverse-height-of-dyadic-count"),
            DeclarationHandle.Create("D5/S3/Weil/RightStripInverseHeight.summable_rightStrip_inverse_height_of_dyadic_count"),
            H("A power saving makes the reciprocal heights summable"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The low zeros form a finite part. On the dyadic band starting at 2^k, the contribution "
                + "to the reciprocal-height sum is at most the weighted count divided by 2^k. A power "
                + "saving in the count makes the resulting bounds a convergent geometric series."))),
            DescribeRole.Theorem))));
}
