using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Generation;

internal sealed class EventHistoryInductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Properties of finite event histories follow from the empty and one-event generation cases.",
        H("Event History Induction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("event-history-generation-induction"),
                DeclarationHandle.Create(
                    "D5/S0/History/Generation/EventHistoryInduction.event_history_induction"),
                H("Event histories admit generation induction"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("P"), Colon, Sp,
                    Operatorname, Grp(F.Id("EventHistory")), To, Sp,
                    Operatorname, Grp(F.Id("Prop")), Comma, Sp,
                    Open, Call("P", F.Id("empty")), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("h"), Colon, Sp,
                    Operatorname, Grp(F.Id("EventHistory")), Comma, Sp,
                    Forall, Sp, F.Id("u"), Colon, Sp,
                    Operatorname, Grp(F.Id("Event")), Comma, Sp,
                    Call("P", F.Id("h")), Sp, Rightarrow, Sp,
                    Call("P", Call("pushBack", F.Id("h"), F.Id("u"))), Close, Close,
                    Sp, Rightarrow, Sp, Forall, Sp, F.Id("h"), Colon, Sp,
                    Operatorname, Grp(F.Id("EventHistory")), Comma, Sp,
                    Call("P", F.Id("h")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The empty event history satisfies P. A nonempty history consists of "
                        + "a shorter history and one last event. The induction hypothesis gives "
                        + "P for the shorter history, and the append hypothesis gives P for the "
                        + "whole history."))),
                DescribeRole.Theorem))));
}
