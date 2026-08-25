using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class BehaviorCompletionUniqueStabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completed behavior range has a unique induced source update.",
        H("Behavior Completion Unique Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("behavior-completion-unique-stability"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/RefinementClosure/"
                        + "BehaviorCompletionUniqueStability."
                        + "behavior_completion_has_unique_induced_update"),
                H("The induced update on completed behavior is unique"),
                StatementSource.FromAuthor(StabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F update a state type X and let q read states into B. No "
                            + "surjectivity assumption is imposed on q.")),
                    Paragraph(Text(
                        "The completion carrier is the realized range of the full future "
                            + "q-itinerary, and the public interface is Mathlib's canonical "
                            + "factorization through that range.")),
                    Paragraph(Text(
                        "The existing itinerary update supplies an induced map making the "
                            + "displayed square commute. Surjectivity of the canonical range "
                            + "factorization cancels its right composition and proves that "
                            + "every other commuting induced map is equal to it.")),
                    Paragraph(Text(
                        "Repository searches found no exact public exists-unique theorem. "
                            + "The proof reuses the canonical completion objects and directly "
                            + "applies the pinned range-factorization surjectivity theorem."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula StabilityFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("B");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula induced = F.Id("induced");
        Formula completionRange = Call("ItineraryRange", update, readout);
        Formula completionProjection = Call(
            "rangeFactorization", Call("completeItinerary", update, readout));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma,
            RowBreak, Grp(),
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(readout, Arrow(state, output)), Comma,
            RowBreak, Grp(),
            Exists, Bang, Sp,
            Typed(induced, Arrow(completionRange, completionRange)), Comma,
            RowBreak, Grp(),
            completionProjection, Sp, Circ, Sp, update, Sp, Eq, Sp,
            induced, Sp, Circ, Sp, completionProjection, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
