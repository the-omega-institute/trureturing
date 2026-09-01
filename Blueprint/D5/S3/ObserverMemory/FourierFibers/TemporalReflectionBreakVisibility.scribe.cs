using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class TemporalReflectionBreakVisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A static scalar observer identifies reflected branches, while one nondegenerate time step separates them.",
        H("Temporal Reflection-Break Visibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflected-branches-time-one-separation"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/TemporalReflectionBreakVisibility.reflected_branches_time_one_separation"),
                H("Time reveals a nondegenerate reflected split"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two reflected branch states collide at time zero. If their modal multipliers differ, the first time step produces different scalar readings.")),
                    Paragraph(Text(
                        "The result formalizes temporal revelation of a pre-existing hidden distinction. It does not claim that the underlying difference is created by observation."))),
                DescribeRole.Theorem))));
}
