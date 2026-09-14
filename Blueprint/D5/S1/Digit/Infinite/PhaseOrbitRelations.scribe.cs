using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class PhaseOrbitRelationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eventual Merging of Infinite Legal Streams.",
        H("Eventual Merging of Infinite Legal Streams"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("phaseorbitrelations-phase-orbit-relations"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/PhaseOrbitRelations.phase_orbit_relations"),
                H("The eventual-merging relations of the successor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The rotation orbit relation on the circle and the relation of eventual merging "
                    + "at possibly different successor times are countable Borel equivalence relations. "
                    + "Two legal streams eventually merge at possibly different times exactly when "
                    + "their phases belong to the same rotation orbit; they merge at a common time "
                    + "exactly when their phases agree. For each positive integer j, all streams of "
                    + "phase minus j times the golden ratio reach the zero row after j steps. Two "
                    + "distinct streams in that fibre remain distinct at every earlier step."))),
                DescribeRole.Theorem))));
}
