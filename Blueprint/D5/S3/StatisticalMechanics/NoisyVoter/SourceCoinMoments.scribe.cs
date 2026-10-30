using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.NoisyVoter;

internal sealed class SourceCoinMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/NoisyVoter/SourceCoinMoments.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/benjaminihelmantovzhukovskii2023noisyvoter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fair opinion moments are determined by the actual ancestral source partition.",
        H("Opinion moments from the source partition"),
        Blocks(Describe.Lean(DescribeId.Create("voter-native-pair-sign-mean"),
            DeclarationHandle.Create(Prefix + "native_pair_sign_mean"),
            H("Two-opinion sign moment"), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text("For any two vertices and natural observation times in the same original model, the expected product of the opinion signs equals the probability of equality of their source labels. The proof partitions into the deterministic finite source sets. Source selection is independent of the fair opinion coins; two distinct labelled coins have zero sign-product mean. The result includes time zero and coincident observations, and uses neither a stationary initial law nor independent observed opinions."))),
            DescribeRole.Theorem)), []));
}
