using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9K33ContactRectanglesDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9K33ContactRectangles.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-coordinate swap rule forces coincident Cartesian products.",
        H("Rectangle closure under contact swaps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eq-prod-of-contact"),
                DeclarationHandle.Create(Owner + "eq_prod_of_contact"),
                H("Coincident Cartesian products"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An initial contact and closure under the two coordinate swaps force both aligned sets to equal the product of their common projections."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("contact-masks-of-contact"),
                DeclarationHandle.Create(Owner + "contactMasks_of_contact"),
                H("Products of displacement sets"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two elementary abelian groups of order four, the displacement masks of a contacting rectangle are the product of the nonzero difference sets of the two projections."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("contact-masks-card-one-three-or-nine"),
                DeclarationHandle.Create(Owner + "contactMasks_card_one_three_or_nine"),
                H("Possible numbers of masks in a contacting rectangle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A two-point projection has one nonzero difference and three or four points have three. The contact mask family therefore has one, three, or nine elements."))),
                DescribeRole.Theorem)),
        []));
}
