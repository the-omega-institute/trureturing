using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class EventOrbitDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An event sequence uniquely determines its state orbit, while the history component records the same sequence one event at a time.",
        H("Event Orbit Data"),
        Blocks(
            Paragraph(
                Text("Given a transition function, an initial state, and a fixed event sequence, any two state sequences that begin at the initial state and obey the transition recurrence are equal. This is the orbit-uniqueness clause of Theorem 18.5.")),
            Paragraph(
                Text("If the history of the initial state is empty and every transition appends its event to history, then at every step the state's history equals the corresponding finite event prefix. This is the history-recording clause of Theorem 18.5.")),
            Paragraph(
                Ref("D5/S0/History/EventOrbitData"),
                Text(" exposes `event_sequence_determines_orbit_and_history`, whose two conjuncts package exactly these orbit and history conclusions.")))));
}
