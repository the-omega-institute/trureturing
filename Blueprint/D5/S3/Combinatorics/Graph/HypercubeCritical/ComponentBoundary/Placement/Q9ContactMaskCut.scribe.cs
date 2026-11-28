using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9ContactMaskCutDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9ContactMaskCut.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-mask axis cuts generate translations of contact fibres. Composing the translations from two cuts can force a further mask.",
        H("Translations forced by three-mask cuts in the nine-cube"),
        Blocks(
            Paragraph(Text("For Hong–Wu–Xia Problem 2 (arXiv:2610.09483v1), consider distance-two contacts on one parity between separated balanced cubic components. Axis cuts restrict which pairs of flips can occur in the mixed part of the Huang operator.")),
            Describe.Lean(
                DescribeId.Create("every-nonempty-axis-cut-has-three-masks"),
                DeclarationHandle.Create(Owner + "every_nonempty_axis_cut_has_three_masks"),
                H("At least three masks across each nonempty cut"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mixed row vanishes at each contact endpoint. A single mask cannot cancel. Two masks force an alternating square whose opposite rows are incompatible after doubling a coordinate of only one mask."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("even-crossing-contact-degree"),
                DeclarationHandle.Create(Owner + "even_crossing_contact_degree"),
                H("Even crossing degree"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At unit weights each incident term of the mixed row is a switching sign, so the zero row contains equally many positive and negative terms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("crossing-contact-degree-two-of-small-cut"),
                DeclarationHandle.Create(Owner + "crossing_contact_degree_two_of_small_cut"),
                H("Two edges at every incident point of a three-mask cut"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each mask has one oriented representative across the cut and at most one contact at a given vertex. The cut bound and even crossing degree force degree two at every incident vertex."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-mask-cut-preserves-contact-fibre"),
                DeclarationHandle.Create(Owner + "three_mask_cut_preserves_contact_fibre"),
                H("The product of the other two masks preserves each contact fibre"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At each endpoint there is exactly one edge to continue along. The weight argument prevents the continuation from closing an alternating square. The second traversal of the initial mask therefore realizes the translate by the product of the other two masks."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-three-mask-cuts-force-contact"),
                DeclarationHandle.Create(Owner + "two_three_mask_cuts_force_contact"),
                H("Two cuts force another mask"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shifts of the shared contact fibre can be composed. When the product moves precisely two axes, composing with the original contact can cancel one of them and force a new distance-two displacement. For the cuts through the mask {2,6} on {2} and {0,3,5,6} with companion masks {2,7}, {2,8} and {0,7}, {6,8}, the forced mask is {0,2}."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightDistanceTwoCenter"))
        ]));
}
