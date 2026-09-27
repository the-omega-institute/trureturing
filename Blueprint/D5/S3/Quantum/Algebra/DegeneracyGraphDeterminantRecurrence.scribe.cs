using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class DegeneracyGraphDeterminantRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Algebra/DegeneracyGraphDeterminantRecurrence";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/kempramgoolam2026degeneracy");
    private static DescribeRole Role(string name) => name is "NewtonE_inv_reindex_fibers" or "NewtonPruningMatrix_apply_low" or "NewtonPruningMatrix_blockTriangular" or "NewtonPruningMatrix_diagonal_block_reindex" or "det_NewtonPruningMatrix_blocks" or "sourceSquare_det_recurrence_mathlib" or "sourceSquare_det_pruning_recurrence" ? DescribeRole.Theorem : DescribeRole.Definition;
    private static DocumentBlock.Describe Declaration(int number, string name) =>
        Describe.Lean(DescribeId.Create($"declaration-{number:00}"), DeclarationHandle.Create($"{Module}.{name}"), H(name),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("This declaration is the exact occupied-degree and pruning recurrence used to reindex the source square. The construction retains actual parent fibers and carries the induced row and column permutations explicitly."))), Role(name));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Occupied-degree reindexing turns the arbitrary-depth source square into a block-triangular pruning recurrence.",
        H("Degeneracy Graph Determinant: Recurrence"),
        Blocks(
            Paragraph(Text("The recurrence owner supplies the canonical bottom and column equivalences, the actual pruning matrix, its low-block and triangular identities, and the signed determinant recurrence. No determinant sign is hidden in an ordering convention: fiber orientation and pruning permutation signs are explicit declarations.")),
            Declaration(1, "OccupiedDegree"), Declaration(2, "DegreeParent"), Declaration(3, "bottomDegreeEquiv"), Declaration(4, "columnDegree"), Declaration(5, "columnDegreeFiberEquiv"), Declaration(6, "columnDegreeEquiv"), Declaration(7, "degreeParentEquiv"), Declaration(8, "pruneBottomEquiv"), Declaration(9, "bottomColumnEquiv"), Declaration(10, "bottomFiberOrderEquiv"), Declaration(11, "NewtonE_inv_reindex_fibers"), Declaration(12, "ancestorPrefix"), Declaration(13, "PruningIndex"), Declaration(14, "pruningRowEquiv"), Declaration(15, "pruningColumnEquiv"), Declaration(16, "NewtonPruningMatrix"), Declaration(17, "pruningDegree"), Declaration(18, "NewtonPruningMatrix_apply_low"), Declaration(19, "NewtonPruningMatrix_blockTriangular"), Declaration(20, "SourceSquare"), Declaration(21, "pruningBlockEquiv"), Declaration(22, "NewtonPruningMatrix_diagonal_block_reindex"), Declaration(23, "det_NewtonPruningMatrix_blocks"), Declaration(24, "pruningPermutation"), Declaration(25, "sourceSquare_det_recurrence_mathlib"), Declaration(26, "sourceSiblingVandermonde"), Declaration(27, "fiberOrientationSign"), Declaration(28, "pruningRecurrenceSign"), Declaration(29, "sourceSquare_det_pruning_recurrence"))));
}
