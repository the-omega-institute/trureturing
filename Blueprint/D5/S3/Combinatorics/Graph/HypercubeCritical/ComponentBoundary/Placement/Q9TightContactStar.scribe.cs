using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9TightContactStarDocument : IScribeDocumentDefinition
{
    private const string Boundary =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Placement = Boundary + "Placement/";
    private const string Owner = Placement + "Q9TightContactStar.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed boundary cancellation constrains tight minimum contact families.",
        H("Tight contacts force full stars"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-tight-contact-full-star"),
                DeclarationHandle.Create(Owner + "tight_contact_cell_full_star"),
                H("The full star and its antipodal copy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Complementary flips match the two contacting parity slices "
                        + "after an antipodal flip. Two distinct vertices of this common slice "
                        + "differ on exactly two axes. A row at distance three from a slice vertex "
                        + "is too close to its antipode in the opposite support. An occupied "
                        + "direction outside the cell would create a minimum displacement "
                        + "outside the tight family. The even boundary equation therefore "
                        + "counts only neighbors in the cell.")),
                    Paragraph(Text("The common slice consists of every leaf of a star on the "
                        + "tight axis set. The two-spoke rows cancel, and the negative Huang "
                        + "sign around each square makes the unit contributions at the star "
                        + "center equal. Cubicity excludes the center. Cancellation there uses "
                        + "at least as many exterior directions as there are leaves."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-minimum-displacements-strict"),
                DeclarationHandle.Create(Owner + "minimum_displacements_card_strict"),
                H("Strictness at distance three or more"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality in the binomial lower bound gives a cell on d + 2 axes. "
                    + "The full-star bound requires twice this number to be at most nine. "
                    + "Thus a nonempty parity family at distance three has at least eleven "
                    + "displacements, and one at distance four has at least sixteen."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-minimum-displacements-strict-signed-defect"),
                DeclarationHandle.Create(Owner + "minimum_displacements_card_strict_of_signed_defect"),
                H("Strictness for a fixed saturated component pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Weighted signed-defect singularity of each balanced connected "
                    + "cubic support provides the needed exterior cancellation on either parity. "
                    + "This supplies the strict count for the component pairs studied in "
                    + "Hong, Wu and Xia’s Problem 2. "
                    + "<https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightContactComplement")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9ActualMinimumDisplacements")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9SignedFragmentBoundary"))
        ]));
}
