using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Provenance;

internal sealed class SeenDirectionAndAppendCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample."
            + "role_admission_direction_nonvacuity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direction witnesses distinguish outgoing contamination from incoming dependency "
            + "closures, and an early ledger append flips admission.",
        H("Access Direction and Early Append Witnesses"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("role-admission-direction-nonvacuity"),
                DeclarationHandle.Create(Declaration),
                H("The direction and append boundaries are non-vacuous"),
                StatementSource.FromAuthor(F.Disp(F.Id("roleAdmissionDirectionNonvacuity"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The DECT access relation reads source objects upstream into accessed "
                            + "objects downstream. The concrete two-element edge false -> true "
                            + "therefore puts true in outgoing Contam of {false}, puts false in "
                            + "the incoming commitment closure of {true}, and puts false in the "
                            + "corrected seen filtration after true is accessed.")),
                    Paragraph(Text(
                        "Reversing that edge removes false from the same one-step seen prefix, "
                            + "so the direction claim is not a naming convention or a constant "
                            + "set. The aggregate theorem consumes all three named direction "
                            + "witnesses.")),
                    Paragraph(Text(
                        "The semantic neighbor uses an old ledger containing an adjudication "
                            + "event and an extended ledger formed by appending a generate event "
                            + "with event id equal to the snapshot decision event. Its dependency "
                            + "touches the commitment closure: the old judge is admissible, while "
                            + "the extended judge is rejected by AdaptiveUseInClosure. This is "
                            + "the required concrete counterexample to dropping the strict "
                            + "post-decision condition."))),
                DescribeRole.Theorem))));
}
