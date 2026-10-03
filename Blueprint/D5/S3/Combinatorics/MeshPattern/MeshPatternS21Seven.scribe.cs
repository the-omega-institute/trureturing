using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MeshPattern;

internal sealed class MeshPatternS21SevenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MeshPattern/MeshPatternS21Seven.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lvzhang2025mesh");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Origin-anchored rectangles containing at most three permutation points carry a growth diagram with seven partition labels.",
        H("Seven-State Growth Diagrams"),
        Blocks(
            Node("mesh-pattern-s21seven-rectangle", "Origin-anchored rectangles", "rectangle",
                "For a word p, a width w and a height h, the rectangle consists of the positions from zero through w minus one whose values in p are at most h. Values outside the word are taken to be zero.", DescribeRole.Definition),
            Node("mesh-pattern-s21seven-ferrersregion", "The ambient Ferrers region", "ferrersRegion",
                "For a nonnegative integer n, the Ferrers region is the union, over m from three through n, of the rectangles of positive cells with width n minus m plus three and height m.", DescribeRole.Definition),
            Node("mesh-pattern-s21seven-active", "Active heights", "active",
                "A height m is active for a word p of parameter n when three is at most m, m is at most n, and the rectangle of width n minus m plus three and height m contains exactly three positions.", DescribeRole.Definition),
            Node("mesh-pattern-s21seven-activeregion", "The active region", "activeRegion",
                "The active region is the union of the positive-cell rectangles of width n minus m plus three and height m over all active heights m.", DescribeRole.Definition),
            Node("mesh-pattern-s21seven-sevenlabel", "The seven partition labels", "SevenLabel",
                "The seven labels represent the empty partition, the partition of one, the row and column partitions of two, and the row, hook and column partitions of three.", DescribeRole.Definition),
            Node("mesh-pattern-s21seven-size", "The size of a label", "size",
                "The size of a label is the number of boxes in its partition: zero for the empty label, one for the single-box label, two for either two-box label and three for any three-box label.", DescribeRole.Definition),
            Node("mesh-pattern-s21seven-sevenedge", "Adjacent partition labels", "sevenEdge",
                "Two labels are joined by an edge when they are equal or when the larger partition is obtained from the smaller by adding one box.", DescribeRole.Definition),
            Node("mesh-pattern-s21seven-seveninverse", "The inverse local rule", "sevenInverse",
                "The inverse local rule assigns a southwest label and a Boolean cell entry to a compatible triple of northeast, northwest and southeast labels. Its finite table is the partition growth rule restricted to the seven labels; triples absent from the table have no assigned value.", DescribeRole.Definition),
            Node("mesh-pattern-s21seven-sevenforward", "The forward local rule", "sevenForward",
                "Given southwest, northwest and southeast labels and a Boolean cell entry, the forward local rule selects the first label, in the order empty, one, two-row, two-column, three-row, hook and three-column, whose inverse rule returns the prescribed southwest label and entry. It has no assigned value if there is no such label.", DescribeRole.Definition),
            Node("mesh-pattern-s21seven-sevendiagram", "The growth diagram", "sevenDiagram",
                "The growth diagram has empty labels on the two coordinate axes. At each positive cell it applies the forward local rule to the three preceding labels and the entry indicating whether the permutation point occupies that cell. An undefined preceding label or local rule makes the new label undefined.", DescribeRole.Definition),
            Node("mesh-pattern-s21seven-seven-state-construction", "Existence on rectangles of size at most three", "seven_state_construction",
                "Let p be a permutation of one through n. Every origin-anchored rectangle with width and height at most n and at most three points has a defined growth-diagram label. The size of that label equals the number of points, and each defined label immediately to its west or south is joined to it by an edge.", DescribeRole.Theorem),
            Node("mesh-pattern-s21seven-seven-order-interpretation", "Increasing and decreasing rectangles", "seven_order_interpretation",
                "Let p be a permutation of one through n, and let an origin-anchored rectangle of width and height at most n contain at most three points and have label L. Its values are strictly increasing in position exactly when L is empty, one, two-row or three-row. They are strictly decreasing in position exactly when L is empty, one, two-column or three-column.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
