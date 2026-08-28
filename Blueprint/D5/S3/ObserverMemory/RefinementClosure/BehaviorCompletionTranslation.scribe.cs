using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class BehaviorCompletionTranslationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A legal system translation induces one and only one map between behavior completions.",
        H("Behavior Completion Translation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("behavior-completion-translation"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/RefinementClosure/"
                        + "BehaviorCompletionTranslation.behavior_completion_translation"),
                H("The induced completion map exists uniquely"),
                StatementSource.FromAuthor(TranslationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source and target completion carriers are the realized ranges of "
                            + "their full future readout itineraries.")),
                    Paragraph(Text(
                        "A state map commuting with the updates and a compatible readout map "
                            + "transport each realized source itinerary coordinatewise to the "
                            + "target completion.")),
                    Paragraph(Text(
                        "The resulting map makes the canonical completion square commute. "
                            + "Surjectivity of the source range factorization makes this map "
                            + "unique.")),
                    Paragraph(Text(
                        "The proof imports the canonical completion transport and projects the "
                            + "commuting and uniqueness clauses of the frozen functoriality law."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TranslationFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula sourceState = F.Id("X");
        Formula targetState = F.Id("Y");
        Formula sourceOutput = F.Id("B");
        Formula targetOutput = F.Id("R");
        Formula sourceStep = F.Id("F");
        Formula sourceReadout = F.Id("q");
        Formula targetStep = F.Id("G");
        Formula targetReadout = F.Id("r");
        Formula stateMap = F.Id("h");
        Formula readoutMap = F.Id("eta");
        Formula induced = Call("C", stateMap);
        Formula sourceCompletion = Call("ItineraryRange", sourceStep, sourceReadout);
        Formula targetCompletion = Call("ItineraryRange", targetStep, targetReadout);
        Formula sourceProjection = Call("completionProjection", sourceStep, sourceReadout);
        Formula targetProjection = Call("completionProjection", targetStep, targetReadout);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(sourceState, type), Comma, Sp,
                Typed(targetState, type), Comma, Sp,
                Typed(sourceOutput, type), Comma, Sp,
                Typed(targetOutput, type), Comma),
            Seq(
                Typed(sourceStep, Arrow(sourceState, sourceState)), Comma, Sp,
                Typed(sourceReadout, Arrow(sourceState, sourceOutput)), Comma),
            Seq(
                Typed(targetStep, Arrow(targetState, targetState)), Comma, Sp,
                Typed(targetReadout, Arrow(targetState, targetOutput)), Comma),
            Seq(
                Typed(stateMap, Arrow(sourceState, targetState)), Comma, Sp,
                Typed(readoutMap, Arrow(sourceOutput, targetOutput)), Comma),
            Seq(
                stateMap, Sp, Circ, Sp, sourceStep, Sp, Eq, Sp,
                targetStep, Sp, Circ, Sp, stateMap, Comma),
            Seq(
                targetReadout, Sp, Circ, Sp, stateMap, Sp, Eq, Sp,
                readoutMap, Sp, Circ, Sp, sourceReadout, Sp, Rightarrow),
            Seq(
                Exists, Sp, Bang, Sp,
                Typed(induced, Arrow(sourceCompletion, targetCompletion)), Comma),
            Seq(
                targetProjection, Sp, Circ, Sp, stateMap, Sp, Eq, Sp,
                induced, Sp, Circ, Sp, sourceProjection, Dot),
        ]));
    }
}
