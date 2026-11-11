using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class KhetanProductPeriodicityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/KhetanProductPeriodicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-cover product fibres feed the six-cell residue dichotomy.",
        H("Product exact-cover bridge at the six-cell boundary"),
        Blocks(
            Paragraph(Text(
                "This module isolates the two-dimensional bridge for a product tile "
                + "{0,1} × {0,b,c}. The one-dimensional theorem "
                + "three_point_tiling_residue is an explicit hypothesis of the bridge: it is "
                + "the unresolved Newman/Fourier input and is not proved or hidden here. "
                + "Given that input, the exact-cover window forces adjacent columns to be "
                + "disjoint and to form a residue-labelled XOR partition, after which the "
                + "existing three_residue_column_dichotomy supplies the horizontal/vertical "
                + "period alternative.")),
            Describe.Lean(
                DescribeId.Create("anchor-bit"),
                DeclarationHandle.Create(Owner + "anchorBit"),
                H("Indicator of a column anchor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "anchorBit(T,x,y) is the natural-number indicator of membership of "
                    + "(x,y) in the anchor set T. It is used to express exact coverage as a "
                    + "sum of zero-one contributions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("one-dimensional-window-count"),
                DeclarationHandle.Create(Owner + "oneDWindowCount"),
                H("One-dimensional three-point window count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "oneDWindowCount(S,b,c,y) sums the indicators of S at the three translated "
                    + "sites y, y-b, and y-c. The separate three_point_tiling_residue input "
                    + "consumes the assertion that this count is exactly one at every y."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("product-window-count"),
                DeclarationHandle.Create(Owner + "productWindowCount"),
                H("Two-column product window count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "productWindowCount(T,b,c,x,y) sums the six possible anchors from columns "
                    + "x-1 and x at the three vertical offsets 0, b, and c. The hypothesis "
                    + "productWindowCount = 1 is the exact unique-cover condition for the "
                    + "product tile."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("product-three-exact-cover-periodic"),
                DeclarationHandle.Create(Owner + "product_three_exact_cover_periodic"),
                H("Exact-cover product fibres force a period"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume b and c are nonzero, distinct, and coprime. Supply explicitly "
                        + "the one-dimensional theorem three_point_tiling_residue for every "
                        + "predicate S satisfying the three-point window count. If every "
                        + "two-column product window has count one, the theorem derives "
                        + "disjoint adjacent columns and a residue/XOR partition.")),
                    Paragraph(Text(
                        "The conclusion is exactly the existing residue dichotomy: either "
                        + "T(x+2,y) ↔ T(x,y) for all x,y, or T(x,y+3) ↔ T(x,y) for all x,y. "
                        + "This is a conditional product branch, not a resolution of the full "
                        + "six-cell orbit-closure problem; the one-dimensional rigidity and "
                        + "orbit-closure extraction remain separate obligations."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/KhetanSixCellResidue"))]));
}
