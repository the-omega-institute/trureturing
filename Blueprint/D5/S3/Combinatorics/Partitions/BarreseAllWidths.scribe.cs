using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class BarreseAllWidthsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/BarreseAllWidths.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/RookTheory/barrese2023levels");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unrestricted normalized shape fiber is finite because its bottom level bounds its width.",
        H("A Width Bound from the Level Data"),
        Blocks(
            Node("barreseallwidths-shapeLevel", "Levels of a normalized shape", "shapeLevel",
                "For a finite Young diagram with bottom-to-top row coordinates, shapeLevel(m,mu,p) is the sum of the lengths of rows mp through mp+m-1. This is the same cell statistic as in a normalized, right-aligned source board.", DescribeRole.Definition),
            Node("barreseallwidths-ShapeFiber", "No imposed width or height bound", "ShapeFiber",
                "ShapeFiber(m,a) contains all finite Young diagrams whose p-th level total equals the p-th entry of a for p below length(a), and zero for every higher p. Neither width nor height appears as a hypothesis. When the entries of a are positive, length(a) is exactly the highest nonempty level.", DescribeRole.Definition),
            Node("barreseallwidths-width-bound", "The derived width bound", "width_bound",
                "For every shape in ShapeFiber(r+1,a), the number of positive source columns is its bottom row length. This length is at most the sum of the r+1 rows in the bottom level, hence at most a_1, with a_1=0 for the empty list. Every row is no longer than the bottom row.", DescribeRole.Theorem),
            Node("barreseallwidths-normalizedPaddingEquiv", "Unique padding to the derived bound", "normalizedPaddingEquiv",
                "There is an exact bijection between ShapeFiber(r+1,a) and NativeFiber(r+1,a_1,a). The zero extension above a forces row (r+1) times length(a) to be empty, hence bounds the height. The width bound permits reading all rows in a_1 column slots. Reflecting to source columns inserts exactly the required number of zero columns at the left. The inverse removes this ambient padding by taking the finite diagram. Thus all positive widths are included, rather than assumed bounded in the definition of the fiber.", DescribeRole.Definition),
            Node("barreseallwidths-all-width-count", "All normalized widths", "all_width_count",
                "For every r and a, the cardinality of the unrestricted normalized shape fiber is F(a,a_1). The exact padding bijection reduces its count to native_count. The empty list has the unique empty shape under the stated zero-extension convention; no infinite horizontal family is substituted for this finite normalized count.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
