using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9MinimumDistanceOperatorDocument : IScribeDocumentDefinition
{
    private const string Cube = "D5/S3/Combinatorics/Graph/HypercubeCritical/";
    private const string Placement = Cube + "ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9MinimumDistanceOperator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum-distance contacts between weighted cube supports.",
        H("The signed coordinate action constrains minimum displacements"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-minimum-ridge-word-parity"),
                DeclarationHandle.Create(Owner + "wordParity"),
                H("Parity of a flip word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each axis in the word toggles the starting parity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-minimum-ridge-contact"),
                DeclarationHandle.Create(Owner + "RidgeContact"),
                H("A ridge and one extension"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Flip the ordered ridge axes and then the extension "
                    + "axis at a vertex of the specified parity in the first support. "
                    + "The extension is absent from the ridge and the endpoint belongs "
                    + "to the second support."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-minimum-ridge-active-axis"),
                DeclarationHandle.Create(Owner + "RidgeActiveAxis"),
                H("Active extension axes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An axis is active if the extended ridge realizes a contact."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-minimum-ridge-contact-cell"),
                DeclarationHandle.Create(Owner + "SameContactCell"),
                H("A cell of contact endpoints"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two endpoints agree at every coordinate except the "
                    + "other active extensions of the ridge."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-minimum-ridge-cell-cancellation"),
                DeclarationHandle.Create(Owner + "minimum_distance_contact_cell_cancels"),
                H("Signed cancellation inside each cell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The two vectors are supported exactly on the selected "
                        + "endpoint parities. The unit-weight image stays in the second "
                        + "support and the image with the chosen coordinate doubled stays "
                        + "in the first. Every cell has signed contact sum zero.")),
                    Paragraph(Text("A signed word shorter than the separation distance has "
                        + "zero pairing across the supports. A repeated axis disappears "
                        + "by the square identity, and each new axis passes the ridge "
                        + "word with the same anticommutation sign. Project onto a "
                        + "coordinate cell and compare the two weightings. The sum in "
                        + "one cell is twice the sum in the cell obtained by flipping "
                        + "the doubled axis. The coordinate involution forces both to vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-minimum-ridge-contact-companion"),
                DeclarationHandle.Create(Owner + "minimum_distance_contact_has_companion"),
                H("A companion with the same displacement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One contact would produce a nonzero signed sum. "
                    + "Thus each contact has a distinct companion with the same "
                    + "displacement in the same cell."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-minimum-contact-displacements"),
                DeclarationHandle.Create(Owner + "minimumDisplacements"),
                H("The family of realized displacements"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Record the differing axes of each pair at the "
                    + "specified distance whose first endpoint has the given parity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-minimum-displacement-count-and-equality"),
                DeclarationHandle.Create(Owner + "minimum_displacements_card_and_equality"),
                H("The number and equality case of minimum displacements"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Two different vertices on the same parity disagree on "
                        + "at least two coordinates. The agreement with the companion "
                        + "therefore supplies at least two other extensions at every "
                        + "ridge. The count of the uniform family gives at least "
                        + "(d + 2) choose 2 displacements at minimum distance d.")),
                    Paragraph(Text("If equality holds, the displacements are precisely the "
                        + "d-subsets of one set of d + 2 axes. Its hypotheses specify the "
                        + "weighted support conditions needed for the two components in "
                        + "Hong, Wu and Xia’s Problem 2. "
                        + "<https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Cube + "TwentyPointEightWord")),
         DocumentEdge.Dependency.Create(GidRef.Create(Cube + "ComponentBoundary/Q9SignedContactCells")),
         DocumentEdge.Dependency.Create(GidRef.Create(Placement + "MinimumContactDisplacementCount"))]));
}
