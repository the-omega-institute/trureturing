using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class MonotoneSeedCalibrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict increases in the mass of nested events require distinct positive-mass seeds.",
        H("Positive-mass witnesses for nested events"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-seed-embedding"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Attribution/MonotoneSeedCalibration.positive_seed_embedding"),
            H("Distinct positive-mass seeds for successive increases"),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let the finite events from index 0 through m be nested and have strictly increasing "
                        + "total real weight. There is an embedding from Fin m into the positive-weight "
                        + "seeds. The image of each index belongs to the next event and not to its current event.")),
                Paragraph(Text(
                    "The weight of each difference equals the increase in event weight. A positive sum "
                        + "gives a positive term. The differences are disjoint because each earlier event "
                        + "is contained in the event subtracted from every later increment.")),
                Paragraph(Text(
                    "For exact masses k/m on the binary grid, at least m positive-weight seeds are needed. "
                        + "Uniform seeds numbered from 0 to m minus 1 attain the bound by choosing label 1 "
                        + "when the seed index is below k. Reflecting the seed and reversing the probability "
                        + "index complements this event and preserves the uniform law."))),
            DescribeRole.Theorem))));
}
