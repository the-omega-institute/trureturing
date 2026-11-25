using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualFilteredLeadingPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The leading cosine and its exponent gap",
        H("The leading cosine and its exponent gap"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-filtered-leading-pair"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualFilteredLeadingPair.actual_filtered_leading_pair"),
            H("The leading cosine and its exponent gap"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The compact average equals the protected cosine with the sign of the explicit formula plus a remainder bounded by the strictly smaller cutoff exponent."))),
            DescribeRole.Theorem))));
}
