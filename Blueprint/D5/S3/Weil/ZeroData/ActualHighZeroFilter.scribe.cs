using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualHighZeroFilterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact positive filters for the actual high zeta zeros",
        H("Compact positive filters for the actual high zeta zeros"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-small-actual-high-zero-filter"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualHighZeroFilter.exists_small_actual_high_zero_filter"),
            H("An arbitrarily short filter for a fixed strip at high ordinates"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Fix a line strictly to the right of one half and a positive support length. A single "
                + "height cutoff works for every choice of protected positive-ordinate zero. For each "
                + "such choice, a compactly supported probability has exponential moment zero at every "
                + "selected high conjugate pair and a nonzero moment at the protected mode. All "
                + "occurrences of the protected zero are excluded before forming the product."))),
            DescribeRole.Theorem))));
}
