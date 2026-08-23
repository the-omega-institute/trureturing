using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class CurrentReadoutRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Evaluation at time zero recovers the current readout from its complete itinerary.",
        H("Current Readout Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("recover-current-readout-from-complete-itinerary"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/CurrentReadoutRecovery."
                        + "recover_current_readout"),
                H("Recover the current readout"),
                StatementSource.FromAuthor(RecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F update a state type X and let q read states into a type B. "
                            + "The complete itinerary of a state records q after every finite "
                            + "iterate of F, while itineraryHead evaluates such an itinerary "
                            + "at time zero.")),
                    Paragraph(Text(
                        "The current readout q is exactly itineraryHead composed with the "
                            + "canonical complete-itinerary map. This is the theorem's sole "
                            + "public clause; it requires no finiteness or injectivity "
                            + "assumption.")),
                    Paragraph(Text(
                        "The proof uses the imported family trajectory constructor directly. "
                            + "At coordinate zero, the zeroth iterate of F is the identity, so "
                            + "the two functions agree on every state.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found the trajectory primitive "
                            + "and the iterate-zero computation, but no existing theorem for "
                            + "this raw recovery equality. The quotient-specific completion "
                            + "readout is a different map."))),
                DescribeRole.Theorem))));

    private static Formula RecoveryFormula()
    {
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("B");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, outputType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            update, Colon, Sp, new Formula.TypeArrow(stateType, stateType), Comma, Sp,
            readout, Colon, Sp, new Formula.TypeArrow(stateType, outputType), Comma, Esc,
            readout, Sp, Eq, Sp, F.Id("itineraryHead"), Sp, Circ, Sp,
            Call("completeItinerary", update, readout), Dot));
    }
}
