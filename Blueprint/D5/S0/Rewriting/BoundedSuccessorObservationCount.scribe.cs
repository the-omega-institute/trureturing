using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class BoundedSuccessorObservationCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded Successor Observation Count",
        H("Bounded Successor Observation Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boundedsuccessorobservationcount-bounded-successor-observation-count"),
                DeclarationHandle.Create("D5/S0/Rewriting/BoundedSuccessorObservationCount.bounded_successor_observation_count"),
                H("First failure times count the finite observations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The strict successor on the finite interval from zero to B first fails from n at time "
                    + "B minus n plus one and remains failed thereafter. Through time h, constant successful "
                    + "readouts give exactly the minimum of B plus one and h plus one observation classes. "
                    + "Arbitrary readouts give at least that many and at most B plus one classes. "
                    + "The first failure times and complete observed futures distinguish all starting states."))),
                DescribeRole.Theorem))));
}
