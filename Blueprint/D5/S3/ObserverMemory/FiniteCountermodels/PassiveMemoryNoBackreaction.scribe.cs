using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FiniteCountermodels;

internal sealed class PassiveMemoryNoBackreactionDocument : IScribeDocumentDefinition
{
    private const string MainHandle =
        "D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction."
            + "passive_memory_no_backreaction";

    private const string WitnessHandle =
        "D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction."
            + "passive_memory_order_witness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Passive upper-triangular memory can retain observer order in an off-diagonal "
            + "holonomy while leaving scalar spectral invariants unchanged.",
        H("Passive Memory No-Backreaction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("passive-memory-no-backreaction"),
                DeclarationHandle.Create(MainHandle),
                H("Passive memory has no scalar backreaction"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Reversing two memory steps produces an explicit nilpotent "
                            + "off-diagonal defect. The defect records order while its trace "
                            + "and determinant vanish.")),
                    Paragraph(Text(
                        "Changing the memory injection at fixed diagonal data leaves trace, "
                            + "determinant, and characteristic polynomial unchanged. The "
                            + "passive triangular lift therefore cannot move scalar spectral "
                            + "roots without a feedback channel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("passive-memory-order-witness"),
                DeclarationHandle.Create(WitnessHandle),
                H("Passive memory can still retain order"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The displayed two-by-two matrices give a concrete noncommuting pair, "
                        + "so the off-diagonal memory channel is not definitionally or "
                        + "vacuously zero."))),
                DescribeRole.Theorem))));
}
