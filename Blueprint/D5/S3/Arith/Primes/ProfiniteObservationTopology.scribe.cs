using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class ProfiniteObservationTopologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cofinal compatible finite phase systems identify the actual topological omega-limit.",
        H("Topology of a cofinal observation clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("profinite-observation-topological-omega-limit"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/ProfiniteObservationTopology.cofinalOmegaHomeomorph"),
                H("The inverse-limit clock is the actual omega-limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Forward and inverse time maps are continuous coordinate by coordinate. "
                    + "Finite cylinders have a common finer observation and can be realized "
                    + "arbitrarily late, proving exact agreement with all tail closures."))),
                DescribeRole.Theorem))));
}
