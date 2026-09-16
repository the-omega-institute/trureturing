using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WeightedCapacity;

internal sealed class ReadoutTopologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuity of the Dyadic Readout.",
        H("Continuity of the Dyadic Readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("readouttopology-result"),
                DeclarationHandle.Create("D5/S3/Analytic/WeightedCapacity/ReadoutTopology.result"),
                H("Finite mass, continuity, and extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural capacity sequence, finite total dyadic mass is equivalent to "
                    + "continuity of the real readout at zero, continuity everywhere in the rational "
                    + "probe topology, and existence of a continuous real extension to the full "
                    + "capacity product with its coordinate topology. When the mass is finite, the "
                    + "extension is unique and equals the supremum of the partial dyadic sums. "
                    + "When the mass is infinite, the readout is discontinuous at every finite state. "
                    + "If infinitely many coordinates have positive capacity, every neighborhood "
                    + "of each finite state contains a different state."))),
                DescribeRole.Theorem))));
}
