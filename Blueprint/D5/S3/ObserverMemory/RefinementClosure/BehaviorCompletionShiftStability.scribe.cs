using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class BehaviorCompletionShiftStabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete behavior interface carries the restricted left-shift dynamics.",
        H("Behavior Completion Shift Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("behavior-completion-shift-stability"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/RefinementClosure/"
                        + "BehaviorCompletionShiftStability."
                        + "behavior_completion_shift_stability"),
                H("Completion intertwines the update and itinerary shift"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The complete itinerary and its realized range are the existing family "
                            + "primitives, constructed from the state update and readout.")),
                    Paragraph(Text(
                        "After one state update, every complete future word is the tail of the "
                            + "previous word. The imported future-itinerary theorem supplies this "
                            + "first public equality directly.")),
                    Paragraph(Text(
                        "The same tail operation restricts to realized words because the shifted "
                            + "word is realized by the updated state. The second public equality "
                            + "states the resulting induced dynamics on the exact completion carrier."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("B");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula point = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula complete = Call("completeItinerary", update, readout);
        Formula projection = Call("rangeFactorization", complete);
        Formula shift = Call("itineraryUpdate", update, readout);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(state, type), Comma, Sp, Typed(output, type), Comma),
            Seq(
                Typed(update, Arrow(state, state)), Comma, Sp,
                Typed(readout, Arrow(state, output)), Comma),
            Seq(
                Open, Forall, Sp, Typed(point, state), Comma, Sp,
                Seq(complete, Open, update, Open, point, Close, Close), Sp, Eq, Sp,
                Call("tail", Seq(complete, Open, point, Close)), Close, Sp, Land),
            Seq(
                projection, Sp, Circ, Sp, update, Sp, Eq, Sp,
                shift, Sp, Circ, Sp, projection, Dot),
        ]));
    }
}
