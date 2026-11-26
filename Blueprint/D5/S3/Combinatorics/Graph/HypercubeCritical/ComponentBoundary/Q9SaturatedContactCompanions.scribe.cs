using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SaturatedContactCompanionsDocument : IScribeDocumentDefinition
{
    private const string Boundary =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Owner = Boundary + "Q9SaturatedContactCompanions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate restrictions on contacts between saturated cube components.",
        H("A two-axis contact forces a companion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-two-flip-contact"),
                DeclarationHandle.Create(Owner + "TwoFlipContact"),
                H("Two-axis contact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A point of the selected parity of the first support is "
                    + "a contact if flipping two distinct named axes lands in the second support."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-active-contact-axis"),
                DeclarationHandle.Create(Owner + "ActiveAxis"),
                H("Active contact axis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With one axis fixed, another axis is active if some "
                    + "point on the selected parity gives a contact along the two axes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-contact-has-companion"),
                DeclarationHandle.Create(Owner + "two_flip_contact_has_companion"),
                H("A companion in the same coordinate cell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take two disjoint supports with no edge between them and a vector "
                        + "supported exactly on one parity of each support. The weighted image of the "
                        + "first vector stays in the first vertex set when the weight of the second "
                        + "contact axis is doubled. The unit-weight image of the second vector stays "
                        + "in the second vertex set. Every contact has a distinct companion across the same two axes, "
                        + "agreeing on all coordinates except possibly the other active axes.")),
                    Paragraph(Text("Freeze the coordinates outside the other active axes and project onto "
                        + "one cell. Separation makes the unit and weighted single-flip pairings zero. "
                        + "Anticommutation moves each weighted flip across the fixed flip. Inactive "
                        + "directions contribute zero and the other active directions leave the cell "
                        + "fixed. Subtracting the two identities gives the contact sum of this cell "
                        + "as twice the sum in the cell with the doubled coordinate flipped. Applying "
                        + "the same equality to that second cell makes both sums zero. One contact "
                        + "alone would contribute a nonzero product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-actual-components-have-companions"),
                DeclarationHandle.Create(Owner + "exists_two_components_with_two_flip_companions"),
                H("At least three partners for an active axis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Any subcubic 258-point support has two distinct actual components "
                        + "that satisfy the companion condition on the false parity in both orders. "
                        + "Every active axis has at least three partners. The companion has the same "
                        + "parity, so it must differ in at least two coordinates, each another active "
                        + "axis. At exactly three partners it is the translate by the other two axes.")),
                    Paragraph(Text("The positive internal Gram vector for each chosen weight has zero "
                        + "crossing to the exterior, by the weighted boundary Gram identity. Undoing "
                        + "the Huang switching and extending by zero supplies the two vectors. "
                        + "The components are chosen before the contact axes and weights. The result "
                        + "restricts joint placements in Hong, Wu and Xia’s open Problem 2. "
                        + "<https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9SignedContactCells")),
         DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9WeightedBoundaryGram")),
         DocumentEdge.Dependency.Create(GidRef.Create(
             "D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TranslationAperiodicity"))]));
}
