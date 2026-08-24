using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class FutureItineraryShiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Updating a state shifts its complete future itinerary by one coordinate.",
        H("Future-Itinerary Shift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("state-update-shifts-complete-future-itinerary"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/FutureItineraryShift."
                    + "future_itinerary_shift"),
                H("A state update shifts the complete future itinerary"),
                StatementSource.FromAuthor(ShiftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary state and readout types, let update advance the state and "
                        + "let readout expose one observation. The complete itinerary at a state "
                        + "is the stream whose n-th coordinate reads the n-fold update.")),
                    Paragraph(Text(
                        "The complete itinerary starting after one update is exactly the stream "
                        + "tail of the itinerary starting at the current state.")),
                    Paragraph(Text(
                        "The statement imports and exposes the repository's canonical "
                        + "completeItinerary and Mathlib's canonical Stream'.tail. The proof "
                        + "applies Function.iterate_succ_apply coordinatewise. Repository and "
                        + "pinned-Mathlib searches found no existing theorem with this exact "
                        + "family statement.")),
                    Paragraph(Text(
                        "This formalizes theorem 41.9. It states the trajectory shift identity "
                        + "without adding finiteness, injectivity, or convergence assumptions."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula>
        {
            Operatorname,
            Grp(F.Id(name)),
            Open,
        };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula ShiftFormula()
    {
        Formula stateType = F.Id("X");
        Formula readoutType = F.Id("B");
        Formula update = F.Id("update");
        Formula readout = F.Id("readout");
        Formula state = F.Id("state");
        Formula itineraryAfterUpdate = Call(
            "completeItinerary", update, readout, Call("update", state));
        Formula currentItinerary = Call("completeItinerary", update, readout, state);

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, readoutType, Comma, Esc,
            Forall, Sp, update, Colon, Sp,
            stateType, Sp, To, Sp, stateType, Comma, Esc,
            Forall, Sp, readout, Colon, Sp,
            stateType, Sp, To, Sp, readoutType, Comma, Esc,
            Forall, Sp, state, InMacro, Sp, stateType, Comma, Esc,
            itineraryAfterUpdate, Sp, Eq, Sp, Call("tail", currentItinerary), Dot));
    }
}
