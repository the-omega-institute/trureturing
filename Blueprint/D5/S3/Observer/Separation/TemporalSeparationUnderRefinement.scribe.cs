using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class TemporalSeparationUnderRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finer observer shrinks every future fiber and cannot postpone an already visible separation.",
        H("Temporal Separation Under Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("separation-time-le-of-refines"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/TemporalSeparationUnderRefinement.separation_time_le_of_refines"),
                H("Refinement cannot delay finite separation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When a coarse readout factors through a finer readout, every finite future fiber of the finer observer lies inside the corresponding coarse fiber.")),
                    Paragraph(Text(
                        "For a pair that the coarse observer eventually separates, the canonical first-separation time of the finer observer is no later. The proof reuses the repository Refines order and separationTime API."))),
                DescribeRole.Theorem))));
}
