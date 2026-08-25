using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class BehaviorCompletionExtensivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The realized behavior completion uniquely refines the current readout.",
        H("Behavior Completion Extensivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("behavior-completion-extensivity"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/BehaviorCompletionExtensivity."
                        + "behavior_completion_extensivity"),
                H("Behavior completion refines the current readout"),
                StatementSource.FromAuthor(ExtensivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F update states and let q be the current readout. The canonical "
                            + "complete itinerary records q after every iterate of F, while its "
                            + "realized range is the effective behavior-completion carrier.")),
                    Paragraph(Text(
                        "There is a unique factor from that realized completion to the readout "
                            + "codomain whose composition with the canonical range factorization "
                            + "recovers q. Thus the completed interface refines q in the source's "
                            + "unique-factor sense.")),
                    Paragraph(Text(
                        "The proof directly applies the exact observer-memory family theorem "
                            + "completion_extensivity; no completion or refinement primitive is "
                            + "redeclared."))),
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
