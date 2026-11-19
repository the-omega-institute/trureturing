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
                + "{0,1} × {0,b,c}, with distinct offsets and gcd(b,c)=1. The classical "
                + "prime-three shift argument proves that every one-dimensional exact-cover "
                + "complement is a single residue class modulo three. This classification "
                + "is proved inside the module. The exact-cover window forces adjacent columns to be "
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
                    + "sites y, y-b, and y-c. When this count is one at every integer and "
                    + "the offsets are primitive, the module proves that S is one residue "
                    + "class modulo three."))),
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
                        "Assume b and c are nonzero, distinct, and coprime. If every "
                        + "two-column product window has count one, the theorem derives "
                        + "disjoint adjacent columns and proves a residue/XOR partition.")),
                    Paragraph(Text(
                        "For each adjacent-column union, the indicator f satisfies "
                        + "f(y)+f(y-b)+f(y-c)=1. Combining this equation at six shifted sites "
                        + "with weights 1,2,2,1,2,1 yields a cubic identity modulo three. "
                        + "Its three diagonal terms are zero-one values, so they are equal; "
                        + "this gives periods 3b and 3c. Bézout gives period three, and summing "
                        + "the cover equation over the three residue classes shows that "
                        + "exactly one class is occupied.")),
                    Paragraph(Text(
                        "The conclusion is exactly the existing residue dichotomy: either "
                        + "T(x+2,y) ↔ T(x,y) for all x,y, or T(x,y+3) ↔ T(x,y) for all x,y. "
                        + "This proves the product branch on the infinite lattice from exact "
                        + "coverage alone. It does not resolve the full six-cell orbit-closure "
                        + "problem: the periodizer and affine-coordinate reduction for an "
                        + "arbitrary full-span six-point tile remain separate obligations."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/KhetanSixCellResidue"))]));
}
