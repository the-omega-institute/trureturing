using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class CompletionExtensivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every readout factors uniquely through its realized complete itinerary.",
        H("Completion Extensivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-extensivity"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/CompletionExtensivity."
                        + "completion_extensivity"),
                H("A readout is refined by its complete itinerary"),
                StatementSource.FromAuthor(ExtensivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F update a state type X and let q read states into B. The "
                            + "complete itinerary records every future q-value, and its "
                            + "realized range is the effective completion carrier.")),
                    Paragraph(Text(
                        "There is a unique map from that realized itinerary range to B whose "
                            + "composition with the canonical range factorization recovers q. "
                            + "This directly expresses the refinement clause on effective "
                            + "images, including the source theorem's uniqueness.")),
                    Paragraph(Text(
                        "The factor evaluates an itinerary at time zero. Current readout "
                            + "recovery proves existence, while surjectivity of the canonical "
                            + "range factorization lets composition cancellation prove "
                            + "uniqueness.")),
                    Paragraph(Text(
                        "Repository search found the canonical completeItinerary, "
                            + "ItineraryRange, and current-readout recovery declarations. "
                            + "Pinned Mathlib supplies rangeFactorization, its surjectivity, "
                            + "and right-composition cancellation; no exact packaged theorem "
                            + "was found."))),
                DescribeRole.Theorem))));

    private static Formula ExtensivityFormula()
    {
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("B");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula factor = F.Id("factor");
        Formula itineraryRange = Call("ItineraryRange", update, readout);
        Formula completion = Call("completeItinerary", update, readout);

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, outputType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            update, Colon, Sp, new Formula.TypeArrow(stateType, stateType), Comma, Sp,
            readout, Colon, Sp, new Formula.TypeArrow(stateType, outputType), Comma, Esc,
            Exists, Bang, Sp, factor, Colon, Sp,
            new Formula.TypeArrow(itineraryRange, outputType), Comma, Esc,
            readout, Sp, Eq, Sp, factor, Sp, Circ, Sp,
            Call("rangeFactorization", completion), Dot));
    }
}
