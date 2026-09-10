using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FiniteCountermodels;

internal sealed class TwoTimeTruthRetentionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Persistence of an event does not force later knowledge of its Boolean value.",
        H("Two-Time Truth Retention"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("persistent-truth-not-always-known"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FiniteCountermodels/TwoTimeTruthRetention.persistent_truth_not_always_known"),
                H("Two-Time Truth Retention"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("PersistentTruthAlwaysKnown universally quantifies over Boolean times and worlds, Boolean observer readouts and event values, and a ledger of a single event. It says that strict time elapse, persistence throughout the interval, and earlier knowledge imply later knowledge.")),
                    Paragraph(Text("Knowledge means that worlds with equal observer readout have equal event value. Persistence means membership in the complete ledger throughout the interval; it does not mean that the observer can read that ledger.")),
                    Paragraph(Text("The existing finite certificate supplies a persistent event whose value is the world bit. The earlier readout distinguishes both worlds and the later readout is constant. Applying that certificate refutes the universal claim without changing the event-value function. This is a finite countermodel, not a claim about human memory mechanisms."))),
                DescribeRole.Theorem))));
}
