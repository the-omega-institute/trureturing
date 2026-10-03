using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MeshPattern;

internal sealed class MeshPatternS21PeelingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lvzhang2025mesh");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Peeling a seven-state boundary reconstructs its cells, conserves row and column weights, and determines the original labels uniquely.",
        H("Peeling Seven-State Boundaries"),
        Blocks(
            Node("mesh-pattern-s21peeling-sevenpath", "Seven-state boundary paths", "sevenPath",
                "A labeled direction word is a seven-state path from a starting label when every rightward step follows an edge from the current label to the next label and every downward step follows an edge from the next label to the current label. The empty word is a path from every label.", DescribeRole.Definition),
            Node("mesh-pattern-s21peeling-sevenslide", "Sliding one column", "sevenSlide",
                "A column slide moves a rightward step across the following downward steps. At each crossed cell the inverse local rule supplies its entry and southwest label. The slide returns the resulting labeled boundary and the entries of the crossed cells, or is undefined if a local rule is undefined.", DescribeRole.Definition),
            Node("mesh-pattern-s21peeling-sevenpeel", "Boundary peeling", "sevenPeel",
                "Boundary peeling recursively processes the remaining direction word, retaining downward steps and sliding each rightward step across the resulting boundary. Its value is a labeled axis path together with a list of cells and Boolean entries, unless a required slide is undefined.", DescribeRole.Definition),
            Node("mesh-pattern-s21peeling-sevenrowweight", "Row weights", "sevenRowWeight",
                "The weight of a row is the sum of the decreases in partition size along the downward steps at that row. A step is at one plus the number of downward steps remaining after it.", DescribeRole.Definition),
            Node("mesh-pattern-s21peeling-sevencolumnweight", "Column weights", "sevenColumnWeight",
                "The weight of a column is the sum of the increases in partition size along rightward steps entering that column. The initial column is specified, and each rightward step increments it by one.", DescribeRole.Definition),
            Node("mesh-pattern-s21peeling-sevenarea", "The area beneath a direction word", "sevenArea",
                "The area is the sum, over all rightward steps, of the number of downward steps that follow them.", DescribeRole.Definition),
            Node("mesh-pattern-s21peeling-sevencells", "The ordered cell list", "sevenCells",
                "The cell list assigns to each rightward step the cells in its new column from its current height down to row one. Columns are processed from the rightmost to the leftmost, and downward steps contribute no cells.", DescribeRole.Definition),
            Node("mesh-pattern-s21peeling-seven-boundary-peeling", "Existence and shape of peeling", "seven_boundary_peeling",
                "Every seven-state path can be peeled. The resulting axis path is again a seven-state path, has all downward steps before all rightward steps, has the same direction multiset and terminal label as the original path, and its returned cells have exactly the ordered cell coordinates of the original direction word. If both the initial and terminal labels are empty, every label on the axis path is empty.", DescribeRole.Theorem),
            Node("mesh-pattern-s21peeling-seven-peeling-conservation", "Conservation and sparsity", "seven_peeling_conservation",
                "For any seven-state path and its peeling, the original weight in each row equals the axis-path weight in that row plus the number of true entries returned in that row. The corresponding equality holds for every column. In each row and each column, at most one returned entry is true.", DescribeRole.Theorem),
            Node("mesh-pattern-s21peeling-seven-peeling-unique", "Uniqueness from the peeled data", "seven_peeling_unique",
                "Two seven-state paths with the same initial label, initial column and direction word are equal whenever their peelings return the same labeled axis path and the same cell entries.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
