using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FiniteCountermodels;

internal sealed class PassiveMemoryNoBackreactionDocument : IScribeDocumentDefinition
{
    private const string HolonomyHandle =
        "D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction."
            + "memory_holonomy_formula";

    private const string CharpolyHandle =
        "D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction."
            + "passive_memory_charpoly_invariant";

    private const string WitnessHandle =
        "D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction."
            + "passive_memory_order_witness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Passive upper-triangular memory can retain observer order in an off-diagonal "
            + "holonomy while leaving scalar spectral roots unchanged.",
        H("Passive Memory No-Backreaction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("passive-memory-holonomy-formula"),
                DeclarationHandle.Create(HolonomyHandle),
                H("Adjacent-swap holonomy is purely off-diagonal"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the canonical injection (L - 1)v, reversing two memory steps "
                        + "changes only the off-diagonal memory entry. The associated trace "
                        + "and determinant vanish by direct corollaries in the Lean module."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("passive-memory-characteristic-polynomial-invariant"),
                DeclarationHandle.Create(CharpolyHandle),
                H("Passive memory leaves the characteristic polynomial unchanged"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At fixed diagonal data, replacing one memory injection by another "
                        + "does not change the characteristic polynomial. The passive "
                        + "triangular lift therefore cannot move scalar spectral roots "
                        + "without a feedback channel."))),
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
