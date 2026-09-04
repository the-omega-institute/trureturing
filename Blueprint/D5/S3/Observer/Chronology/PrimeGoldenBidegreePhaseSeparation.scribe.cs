using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenBidegreePhaseSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenBidegreePhaseSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One scalar Euler phase sample can alias bidegrees, while the complete time trajectory recovers the bidegree.",
        H("Prime-Golden Bidegree Phase Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-phase-observation-boundary"),
                DeclarationHandle.Create(
                    Prefix + "prime_golden_phase_observation_boundary"),
                H("A snapshot aliases and the complete phase trajectory separates"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At time zero every bidegree has unit phase, giving an explicit noninjective scalar sample.")),
                    Paragraph(Text(
                        "For distinct bidegrees, the half-beat of their nonzero frequency difference sends the relative phase to minus one and separates them.")),
                    Paragraph(Text(
                        "The full scalar trajectory therefore recovers the two count coordinates, while Magnus or Hopf data is still required for event order."))),
                DescribeRole.Theorem))));
}
