using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class BehaviorCompletionFunctorialityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Behavior completion transports legal system translations functorially.",
        H("Behavior Completion Functoriality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("behavior-completion-is-functorial"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/RefinementClosure/"
                        + "BehaviorCompletionFunctoriality."
                        + "behavior_completion_is_functorial"),
                H("Completion preserves translations and their composition"),
                StatementSource.FromAuthor(FunctorialityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A system translation consists of a state map commuting with the "
                            + "updates and a readout map commuting with the observations. "
                            + "It sends each realized source itinerary coordinatewise to a "
                            + "realized target itinerary.")),
                    Paragraph(Text(
                        "The induced completion map makes the canonical projection square "
                            + "commute. Surjectivity of the source range factorization makes "
                            + "this map unique, while coordinate shifting proves that it "
                            + "semiconjugates the completed updates.")),
                    Paragraph(Text(
                        "Coordinatewise transport by the identity readout map is the identity "
                            + "on completion, and transport by a composite readout map is the "
                            + "composite of the two induced completion maps.")),
                    Paragraph(Text(
                        "The implementation reuses completeItinerary, ItineraryRange, "
                            + "itineraryUpdate, and the pinned range-factorization and "
                            + "semiconjugacy laws. Repository and library searches found no "
                            + "existing declaration packaging all five displayed clauses."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula FunctorialityFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula xType = F.Id("X");
        Formula yType = F.Id("Y");
        Formula zType = F.Id("Z");
        Formula bType = F.Id("B");
        Formula rType = F.Id("R");
        Formula sType = F.Id("S");
        Formula sourceStep = F.Id("F");
        Formula middleStep = F.Id("G");
        Formula targetStep = F.Id("H");
        Formula sourceReadout = F.Id("q");
        Formula middleReadout = F.Id("r");
        Formula targetReadout = F.Id("s");
        Formula firstStateMap = F.Id("h");
        Formula secondStateMap = F.Id("k");
        Formula firstReadoutMap = F.Id("eta");
        Formula secondReadoutMap = F.Id("theta");
        Formula hstep = F.Id("hstep");
        Formula kstep = F.Id("kstep");
        Formula hreadout = F.Id("hreadout");
        Formula kreadout = F.Id("kreadout");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula sourceProjection = Call(
            "rangeFactorization", Call("completeItinerary", sourceStep, sourceReadout));
        Formula middleProjection = Call(
            "rangeFactorization", Call("completeItinerary", middleStep, middleReadout));
        Formula sourceCompletion = Call("ItineraryRange", sourceStep, sourceReadout);
        Formula middleCompletion = Call("ItineraryRange", middleStep, middleReadout);
        Formula firstTransport = Call(
            "completionTransport",
            sourceStep, sourceReadout, middleStep, middleReadout,
            firstStateMap, firstReadoutMap, hstep, hreadout);
        Formula secondTransport = Call(
            "completionTransport",
            middleStep, middleReadout, targetStep, targetReadout,
            secondStateMap, secondReadoutMap, kstep, kreadout);
        Formula compositeReadoutProof = Grp(
            Lambda, Sp, x, Colon, Sp, xType, Comma, Sp,
            Call(
                "trans",
                Apply(kreadout, Apply(firstStateMap, x)),
                Call("congrArg", secondReadoutMap, Apply(hreadout, x))));
        Formula compositeTransport = Call(
            "completionTransport",
            sourceStep, sourceReadout, targetStep, targetReadout,
            Seq(secondStateMap, Sp, Circ, Sp, firstStateMap),
            Seq(secondReadoutMap, Sp, Circ, Sp, firstReadoutMap),
            Call("trans", hstep, kstep),
            compositeReadoutProof);
        Formula sourceShift = Call("itineraryUpdate", sourceStep, sourceReadout);
        Formula middleShift = Call("itineraryUpdate", middleStep, middleReadout);
        Formula candidate = Phi;
        Formula hreadoutLaw = Seq(
            Forall, Sp, Typed(x, xType), Comma, Sp,
            Apply(middleReadout, Apply(firstStateMap, x)), Sp, Eq, Sp,
            Apply(firstReadoutMap, Apply(sourceReadout, x)));
        Formula kreadoutLaw = Seq(
            Forall, Sp, Typed(y, yType), Comma, Sp,
            Apply(targetReadout, Apply(secondStateMap, y)), Sp, Eq, Sp,
            Apply(secondReadoutMap, Apply(middleReadout, y)));
        Formula identityTransport = Call(
            "completionTransport",
            sourceStep, sourceReadout, sourceStep, sourceReadout,
            F.Id("id"), F.Id("id"), F.Id("idLeft"),
            Grp(Lambda, Sp, x, Colon, Sp, xType, Comma, Sp, F.Id("rfl")));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(xType, type), Comma, Sp,
                Typed(yType, type), Comma, Sp, Typed(zType, type), Comma, Sp,
                Typed(bType, type), Comma, Sp, Typed(rType, type), Comma, Sp,
                Typed(sType, type), Comma),
            Seq(
                Typed(sourceStep, Arrow(xType, xType)), Comma, Sp,
                Typed(sourceReadout, Arrow(xType, bType)), Comma),
            Seq(
                Typed(middleStep, Arrow(yType, yType)), Comma, Sp,
                Typed(middleReadout, Arrow(yType, rType)), Comma),
            Seq(
                Typed(targetStep, Arrow(zType, zType)), Comma, Sp,
                Typed(targetReadout, Arrow(zType, sType)), Comma),
            Seq(
                Typed(firstStateMap, Arrow(xType, yType)), Comma, Sp,
                Typed(firstReadoutMap, Arrow(bType, rType)), Comma),
            Seq(
                Typed(secondStateMap, Arrow(yType, zType)), Comma, Sp,
                Typed(secondReadoutMap, Arrow(rType, sType)), Comma),
            Seq(
                Typed(hstep, Call(
                    "Semiconj", firstStateMap, sourceStep, middleStep)), Comma),
            Seq(
                Typed(kstep, Call(
                    "Semiconj", secondStateMap, middleStep, targetStep)), Comma),
            Seq(
                Typed(hreadout, Grp(hreadoutLaw)), Comma),
            Seq(
                Typed(kreadout, Grp(kreadoutLaw)), Sp, Rightarrow),
            Seq(
                middleProjection, Sp, Circ, Sp, firstStateMap, Sp, Eq, Sp,
                firstTransport, Sp, Circ, Sp, sourceProjection, Sp, Land),
            Seq(
                Open, Forall, Sp,
                Typed(candidate, Arrow(sourceCompletion, middleCompletion)), Comma, Sp,
                middleProjection, Sp, Circ, Sp, firstStateMap, Sp, Eq, Sp,
                candidate, Sp, Circ, Sp, sourceProjection, Sp, Rightarrow, Sp,
                candidate, Sp, Eq, Sp, firstTransport, Close, Sp, Land),
            Seq(
                Call("Semiconj", firstTransport, sourceShift, middleShift), Sp, Land),
            Seq(
                identityTransport, Sp, Eq, Sp, F.Id("id"), Sp, Land),
            Seq(
                compositeTransport, Sp, Eq, Sp,
                secondTransport, Sp, Circ, Sp, firstTransport, Dot),
        ]));
    }
}
