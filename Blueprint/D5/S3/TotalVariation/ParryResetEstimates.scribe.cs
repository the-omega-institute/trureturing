using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryResetEstimatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/ParryResetEstimates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-step common mass.",
        H("Three-step common mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parryresetestimates-parry-three-step-minorization"),
                DeclarationHandle.Create(Prefix + "parry_three_step_minorization"),
                H("Three-step common mass"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("From every signed suffix state, the words 000 and 010 reach the two zero-suffix signs. Both path products equal p cubed divided by the starting suffix weight. Each is at least one eighth, uniformly in k. Thus the three-step transition has common mass one quarter on the two zero-suffix states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parryresetestimates-parry-suffix-tail"),
                DeclarationHandle.Create(Prefix + "parry_suffix_tail"),
                H("The uniform golden tail"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The total stationary mass at suffix at least L is bounded by the golden ratio to the integer power 2 minus L. The proof bounds each signed mass by one half of the reciprocal-golden geometric term and sums the finite interval. Empty tails are included."))),
                DescribeRole.Theorem))));
}
