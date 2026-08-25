using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class BehaviorCompletionStabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The effective behavior completion is stable under the source update.",
        H("Behavior Completion Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("behavior-completion-stability"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionStability."
                        + "behavior_completion_is_stable"),
                H("Behavior completion carries the canonical shift dynamics"),
                StatementSource.FromAuthor(StabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F update a state space X, and let q be a surjective interface onto "
                            + "its effective output codomain.")),
                    Paragraph(Text(
                        "The behavior completion is constructed as the realized range of the "
                            + "full future q-itinerary. Its interface map is the canonical "
                            + "factorization through that range.")),
                    Paragraph(Text(
                        "The induced map is the existing itinerary shift: it drops the current "
                            + "coordinate and advances every remaining future coordinate by one. "
                            + "Because a shifted realized itinerary is realized by F(x), the map "
                            + "stays on the exact effective-image carrier.")),
                    Paragraph(Text(
                        "The displayed commutation equation is precisely interface stability. "
                            + "No parallel completion or shift definition is introduced."))),
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
        Formula induced = F.Id("Fbar");
        Formula completionRange = Call("ItineraryRange", update, readout);
        Formula completionProjection = Call(
            "rangeFactorization", Call("completeItinerary", update, readout));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Comma,
            RowBreak, Grp(),
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(readout, Arrow(state, output)), Comma,
            RowBreak, Grp(),
            Call("Surjective", readout), Sp, Rightarrow,
            RowBreak, Grp(),
            Exists, Sp,
            Typed(induced, Arrow(completionRange, completionRange)), Comma,
            RowBreak, Grp(),
            completionProjection, Sp, Circ, Sp, update, Sp, Eq, Sp,
            induced, Sp, Circ, Sp, completionProjection, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
