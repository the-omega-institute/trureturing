using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryResetLawDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/ParryResetLaw.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stationary signed Parry law.",
        H("The stationary signed Parry law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parryresetlaw-parry-stationary-law"),
                DeclarationHandle.Create(Prefix + "parry_stationary_law"),
                H("The stationary signed Parry law"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected root gives positive suffix weights h_j between p and one. Their weighted sum S is at least one. The reset and increment entries are nonnegative and each row sums to one. The signed law p to the j times h_j divided by 2S is normalized, invariant under sign complement, and stationary. Incoming reset flow is summed over every suffix, while every positive suffix has exactly one increment predecessor."))),
                DescribeRole.Theorem))));
}
