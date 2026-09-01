using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class TemporalReflectionSeparationTimeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nondegenerate reflected spectral pair has canonical first-separation time one.",
        H("Temporal Reflection Separation Time"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflected-branch-separation-time-eq-one"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/TemporalReflectionSeparationTime.reflected_branch_separation_time_eq_one"),
                H("Reflected branches first separate at time one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The reflected branch states collide at time zero and, when their reciprocal multipliers differ, separate at the first subsequent observation.")),
                    Paragraph(Text(
                        "The proof instantiates the repository's canonical separationTime and observedAt APIs; it does not introduce another break-depth definition."))),
                DescribeRole.Theorem))));
}
