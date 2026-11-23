using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class SourceOverlapCouplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Splitting the unit interval at a source mass realizes compatible overlaps.",
        H("Realizing prescribed overlaps with a source event"),
        Blocks(
            Describe.Lean(DescribeId.Create("nested-events"), DeclarationHandle.Create(
                "D5/S1/Words/AdmissibleWords/SourceOverlapCoupling.exists_nested_events"),
                H("Nested events with prescribed source overlaps"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A marginal and its proposed overlap with a fixed source prescribe two masses, "
                    + "one inside the source and one outside. Each must fit inside its part of the "
                    + "unit interval. Both masses must be nondecreasing across each required "
                    + "inclusion, and the source must have full overlap with itself. Take the initial "
                    + "interval of the prescribed length in each part. Their union is Lebesgue "
                    + "measurable and realizes the marginal, the source overlap and every "
                    + "required inclusion."))),
                DescribeRole.Theorem))));
}
