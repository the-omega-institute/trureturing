using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickComponentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive matrix components construct one actual finite reverse test with its entire hockey profile.",
        H("Actual reverse tests from positive components"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-hockey-components-profile"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/MaximalHockeyStickComponents."
                        + "reverse_test_from_components_profile"),
                H("The same test realizes the cost and every threshold"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive components G_i and 0 <= x_i <= 1, the construction prepares "
                        + "the two sums x_i G_i and (1-x_i) G_i with actual density states. "
                        + "Its quadratic cost and its classical hockey profile at every real "
                        + "threshold are computed from those same labels. Zero components "
                        + "have zero classical mass, and an empty carrier uses no labels."))),
                DescribeRole.Theorem))));
}
