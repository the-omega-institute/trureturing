using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class ProjectionFramesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frames for a proper projection and its complement",
        H("Frames for a proper projection and its complement"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-complementary-frames"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/ProjectionFrames.exists_complementary_frames"),
            H("Frames for a proper projection and its complement"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A nonzero proper Hermitian projector admits complementary isometric frames of positive ranks. Together their range projectors sum to the identity."))),
            DescribeRole.Theorem))));
}
