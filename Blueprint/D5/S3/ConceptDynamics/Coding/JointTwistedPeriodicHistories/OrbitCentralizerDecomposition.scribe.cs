using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.JointTwistedPeriodicHistories;

internal sealed class OrbitCentralizerDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/JointTwistedPeriodicHistories/OrbitCentralizerDecomposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The joint twisted coefficient count is an orbit sum weighted by the centralizer cardinality.",
        H("Orbit--centralizer decomposition of joint twisted returns"),
        Blocks(
            Paragraph(Text(
                "The existing signed-gcd cardinality is a raw sum over the group coordinate. "
                + "The new result reindexes that sum through the finite conjugation action and "
                + "counts each orbit element with the stabilizer, identified here with the centralizer.")),
            Describe.Lean(
                DescribeId.Create("joint-twisted-orbit-centralizer-cardinality"),
                DeclarationHandle.Create(Prefix + "jointTwistedPeriod_card_orbit_centralizer"),
                H("Orbit--centralizer weighted coefficient count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every compatible pair of twisted returns, the diagonal coefficient sum "
                    + "equals the sum over the conjugation orbit of the signed gcd twist, with "
                    + "the cardinality of its centralizer multiplying each coefficient."))),
                DescribeRole.Theorem))));
}
