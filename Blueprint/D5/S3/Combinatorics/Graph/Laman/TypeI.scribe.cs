using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Laman;

internal sealed class TypeIDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Laman/TypeI.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/chen2026combinatorialrigidity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real planar Type I Henneberg rigidity preservation.",
        H("Type I geometric preservation"), Blocks(
            Describe.Lean(DescribeId.Create("typei-0"), DeclarationHandle.Create(Prefix + "typeI_isInfinitesimallyRigid_extend"),
                H("Type I kernel injection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("If a finite graph has an infinitesimally rigid placement in the plane and the new point has linearly independent displacement vectors to two distinct attachment vertices, the Option extension is infinitesimally rigid. The proof injects the extended kernel into the old kernel by restriction to existing vertices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("typei-1"), DeclarationHandle.Create(Prefix + "exists_off_line_off_finite_dim_two"),
                H("An off-line point outside a finite set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Given two distinct points in the real plane and a finite set, there is a point outside that set whose displacement vectors to the two points are linearly independent."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("typei-2"), DeclarationHandle.Create(Prefix + "typeI_isGenericallyRigidInj_two"),
                H("Type I preserves injective generic rigidity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite graph, an injectively generically rigid planar placement remains injectively generically rigid after a Type I move at distinct attachment vertices. The new point is chosen off the old image and off the attachment line."))), DescribeRole.Theorem)), []));
}
