using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9TightContactComplementDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9TightContactComplement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate symmetries at equality in the minimum displacement bound.",
        H("Complementary flips and antipodal slices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-tight-contact-flip-complement"),
                DeclarationHandle.Create(Owner + "minimum_contact_flip_complement"),
                H("The complementary axes preserve each contact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the separated supports admit the weighted exterior "
                    + "cancellation functions in the statement. If the minimum displacements "
                    + "of length d on one parity are all d-subsets of d + 2 axes, fix a "
                    + "displacement and erase one axis. "
                    + "The only other active extensions are the two axes outside that displacement. "
                    + "The companion has the same parity and differs from the original endpoint, "
                    + "so it flips both axes. The two endpoints of the contact move together "
                    + "and keep the same displacement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-tight-contact-cell-antipodes"),
                DeclarationHandle.Create(Owner + "minimum_contact_cell_antipodes"),
                H("The antipodal flip matches the slices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same weighted cancellation and tight-family hypotheses, "
                        + "fix the coordinates outside the d + 2 axes and compare a vertex "
                        + "of the first support with the antipode of a vertex of the second "
                        + "support on the same parity. Separation and the antipodal distance "
                        + "identity force their distance to be zero or two.")),
                    Paragraph(Text("At distance zero the vertices already match. At distance two "
                        + "the original pair realizes the minimum distance, and the complementary "
                        + "flip puts each antipode in the other support. This gives antipodal "
                        + "matching in cells meeting both of the specified parity slices. "
                        + "<https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9MinimumDistanceOperator"))]));
}
