using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class PartialForwardOrderLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Likelihood and posterior for partial observations of independent binary orders.",
        H("Partial observations of binary forward orders"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partial-forward-order-likelihood"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw.partial_forward_order_likelihood"),
                H("One factor of one half per observed position"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take finitely many positions, each with two distinct available values. "
                        + "Assign an independent uniform order to its two slots. A fixed "
                        + "observation may specify neither, one, or both slots at each position.")),
                    Paragraph(Text(
                        "The observation is compatible if each specified value is available "
                        + "at its position and two specified slots at the same position have "
                        + "different values. If s is the set of positions with a specified "
                        + "slot, a compatible observation has outer mass two to the power "
                        + "minus the size of s. An incompatible observation has mass zero.")),
                    Paragraph(Text(
                        "One specified slot determines the order of two distinct values. "
                        + "A second specified slot tests the already determined order. "
                        + "The compatible tables thus form the product cylinder that fixes "
                        + "one order at each observed position."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-forward-order-posterior"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw.partial_forward_order_posterior"),
                H("The posterior is the prior conditioned on compatibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a world sampled from a probability mass function determine the two "
                        + "distinct available values at every position. Draw the uniform order "
                        + "table independently. A given partial observation has the same "
                        + "number of observed positions in every world.")),
                    Paragraph(Text(
                        "If the joint observation has positive mass, the posterior mass of "
                        + "each set of worlds is its prior mass intersected with the compatible "
                        + "worlds, divided by the prior mass of all compatible worlds. "
                        + "The common positive likelihood cancels from the two outer masses."))),
                DescribeRole.Theorem))));
}
