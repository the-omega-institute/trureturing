using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MeshPattern;

internal sealed class MeshPatternS21BoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lvzhang2025mesh");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The active Ferrers region has a labeled boundary compatible with the seven-state local rule, and every active rectangle contributes a specified boundary corner.",
        H("Boundaries of Active Ferrers Regions"),
        Blocks(
            Node("mesh-pattern-s21boundary-sevenboundary", "A labeled boundary", "sevenBoundary",
                "A boundary direction word uses false for a downward step and true for a rightward step. Starting from the given column and the total number of downward steps, the labeled boundary pairs each direction with the label at the endpoint of its step.", DescribeRole.Definition),
            Node("mesh-pattern-s21boundary-sevenoutline", "The outline of a region", "sevenOutline",
                "Starting at a specified column and row, the outline moves right when the next cell lies in the region and the column bound has not been reached; otherwise it moves down. It ends when the row is zero.", DescribeRole.Definition),
            Node("mesh-pattern-s21boundary-transpose", "Partition transposition", "transpose",
                "Transposition exchanges the two-box row and column labels and the three-box row and column labels. It fixes the empty, one-box and hook labels.", DescribeRole.Definition),
            Node("mesh-pattern-s21boundary-seven-active-outline", "The active outline", "seven_active_outline",
                "For a permutation of one through n, the active outline starts at column zero and row n and has n downward steps. Its cell list has no repetitions and consists exactly of the active region. The boundary labels form a seven-state path ending with the empty label, and at every listed cell the inverse local rule recovers the southwest label and the permutation entry.", DescribeRole.Theorem),
            Node("mesh-pattern-s21boundary-seven-corner-boundary", "Corners at active heights", "seven_corner_boundary",
                "For a permutation of one through n and an active height m, the active outline factors into a prefix, a rightward step and a suffix such that the prefix has n minus m plus two rightward steps and the suffix has m downward steps. Thus the selected step ends at column n minus m plus three and row m.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
