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
                    Open, Call("P", D(1)), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("h"), Colon, Sp,
                    Operatorname, Grp(F.Id("EventHistory")), Comma, Sp,
                    Forall, Sp, F.Id("u"), Colon, Sp,
                    Operatorname, Grp(F.Id("Event")), Comma, Sp,
                    Call("P", F.Id("h")), Sp, Rightarrow, Sp,
                    Call("P", Call("generate", F.Id("h"), F.Id("u"))), Close, Close,
                    Sp, Rightarrow, Sp, Forall, Sp, F.Id("h"), Colon, Sp,
                    Operatorname, Grp(F.Id("EventHistory")), Comma, Sp,
                    Call("P", F.Id("h")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The empty event history satisfies P, and P is preserved when generate "
                        + "appends one event. Every finite EventHistory therefore satisfies P. "
                        + "This closes only Definition 2.3 clause 3, the generation-induction "
                        + "principle; it makes no claim about the neighboring clauses.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. FreeMonoid.inductionOn' is "
                        + "the existing induction engine, while FreeMonoid.reverse_mul, "
                        + "FreeMonoid.reverse_of, and FreeMonoid.reverse_reverse transport its "
                        + "left-generator step to the repository's right-appending generate. "
                        + "The Lean declaration is a thin wrapper over those library results and "
                        + "reuses the existing EventHistory carrier."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/History/HistoryCarrier"))]));
}
