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
                DescribeRole.Theorem))));
}
