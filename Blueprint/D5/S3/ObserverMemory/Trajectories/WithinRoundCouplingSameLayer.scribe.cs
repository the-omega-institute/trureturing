using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class WithinRoundCouplingSameLayerDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer."
            + "IsSameLayerInRound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Definition 45.2 has an explicit augmented-system interface; Proposition "
            + "45.3 remains open at its independent Delta condition.",
        H("Within-Round Coupling and Same-Layer Evaluation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("same-layer-in-round"),
                DeclarationHandle.Create(Declaration),
                H("Same-layer data for an augmented recorded system"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let e be a positive round index. The append-only operations R and "
                            + "the maps q1 : X -> A, controlledUpdate : RoundIndex -> "
                            + "X x Y2 -> X, and q2 : Lambda1 -> Y2 are exactly the data of "
                            + "the recorded observer at that round.")),
                    Paragraph(Text(
                        "WithinRoundDecoupled says that controlledUpdate e has the same value "
                            + "for every pair of Y2 inputs at each state. Proposition 45.3 "
                            + "assumes the negation of precisely that condition.")),
                    Paragraph(Text(
                        "CrossRoundUpdateSchedule records the separate inter-round clause. The "
                            + "update at nextRound e is selected by a function receiving q2 of "
                            + "the preceding round's terminal record. IsSecondLayerObserver is the "
                            + "all-round predicate requiring WithinRoundDecoupled at every round.")),
                    Paragraph(Text(
                        "AugmentedSingleSystem gives dynamics, readout, and deltaEvaluation as "
                            + "separate fields. At Definition 45.2 the carrier is typed as X x "
                            + "Lambda1, the readout codomain as A x Y2, and the quotient as the "
                            + "kernel quotient of jointReadout. No constructor derives "
                            + "deltaEvaluation from q2.")),
                    Paragraph(Text(
                        "IsSameLayerInRound requires three independent facts: the supplied readout "
                            + "equals jointReadout, the supplied dynamics equals Definition 45.1's "
                            + "closed-loop jointRoundUpdate, and the supplied Delta/evaluation "
                            + "diagonal agrees with q2 descended to the joint quotient.")),
                    Paragraph(Text(
                        "Proposition 45.3 is intentionally not declared as proved. The coupling "
                            + "premise constrains controlledUpdate but supplies no relation for the "
                            + "independently given deltaEvaluation; "
                            + "coupling_does_not_force_delta_diagonal formalizes this obstruction. "
                            + "Re-entry requires source support deriving the already-given Delta "
                            + "diagonal law from coupling, or an independently specified Delta "
                            + "construction carrying that law. Defining Delta from q2 solely to "
                            + "make the equality reflexive is not a valid re-entry.")),
                    Paragraph(Text(
                        "EstablishedClosureNonimplications remains the exact proposition already "
                            + "proved by closure_nonimplication_triple for Sections 32.10 and 33.10. "
                            + "That theorem does not provide the missing Delta relation."))),
                DescribeRole.Definition))));
}
