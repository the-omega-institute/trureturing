using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FixedPoint;

internal sealed class SimplexMeshDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/mathxmum2025brouwer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dominant lattice cells constrain coordinate minima.",
        H("Dominant lattice cells constrain coordinate minima"),
        Blocks(Describe.Lean(
            DescribeId.Create("mathxmum-simplexmesh"),
            DeclarationHandle.Create("D5/S3/Geometry/FixedPoint/SimplexMesh.size_bound_key"),
            H("Dominant lattice cells constrain coordinate minima"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For positive n and l, lattice points are nonnegative integer coordinates indexed by Fin n, bounded by l and summing to l. For each selected index, compare that coordinate first, then break ties by the lexicographic order of the complete lattice tuple. A nonempty cell sigma dominant for these exact orders with color set C satisfies l < sum over C of coordinate minima plus |C|.")),
                Paragraph(Text("Assuming the opposite bound, assign one more than each selected coordinate minimum, zero elsewhere, and put the residual mass into coordinate zero. The resulting genuine lattice point contradicts dominance.")),
                Paragraph(Text("The result and proof source are attributed to Math_XMUM's MIT-licensed Brouwer repository at its immutable revision. No mathematical novelty is claimed. The combinatorics and real fixed-point argument establish no tetrahedral geometry, marked gluing, trajectory invariance, uniqueness, geometric Hessian, or convergence conclusion."))),
            DescribeRole.Theorem))));
}
