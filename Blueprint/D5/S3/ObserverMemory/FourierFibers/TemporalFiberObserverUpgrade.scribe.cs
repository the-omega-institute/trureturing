using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class TemporalFiberObserverUpgradeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Enlarging a time window shrinks compatible observation fibers.",
        H("Temporal Fiber Observer Upgrade"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("same-temporal-fiber-antitone"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/TemporalFiberObserverUpgrade.same_temporal_fiber_antitone"),
                H("Temporal fibers are antitone in the observation window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every equality witnessed on a larger finite time window restricts to equality on any smaller window, so adding observation times can only refine the observer kernel.")),
                    Paragraph(Text(
                        "Under separated finite modes, the first full time window has subsingleton fibers. This records observation-depth refinement without asserting thermodynamic irreversibility."))),
                DescribeRole.Theorem))));
}
