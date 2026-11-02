using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Laman;

internal sealed class TypeIDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Laman/TypeI.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/chen2026combinatorialrigidity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real planar Henneberg rigidity preservation.",
        H("Type I and Type II geometric preservation"), Blocks(
            Describe.Lean(DescribeId.Create("typei-0"), DeclarationHandle.Create(Prefix + "exists_not_mem_span_singleton_dim_two"),
                H("A point outside a nonzero plane line"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A nonzero vector span in the real plane is proper, so a point outside it exists."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("typei-1"), DeclarationHandle.Create(Prefix + "typeI_isInfinitesimallyRigid_extend"),
                H("Type I kernel injection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("If a finite graph has an infinitesimally rigid planar placement and the new point has independent displacement vectors to two attachments, the Type I extension is infinitesimally rigid."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("typei-2"), DeclarationHandle.Create(Prefix + "exists_off_line_off_finite_dim_two"),
                H("An off-line point outside a finite set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Given two distinct planar points and a finite set, there is a point outside that set with linearly independent displacement vectors to both points."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("typei-3"), DeclarationHandle.Create(Prefix + "typeI_isGenericallyRigidInj_two"),
                H("Type I preserves injective generic rigidity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Injective generic rigidity in the plane is preserved by a Type I Henneberg move at distinct attachments."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("typei-4"), DeclarationHandle.Create(Prefix + "typeII_collinear_inner_combo"),
                H("The Type II deleted-edge identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The collinear Type II placement identity recovers the deleted-edge rigidity equation from the two new-edge equations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("typei-5"), DeclarationHandle.Create(Prefix + "typeII_isInfinitesimallyRigid_extend"),
                H("Type II kernel injection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A collinear Type II extension with an independent third displacement preserves infinitesimal rigidity in the plane."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("typei-6"), DeclarationHandle.Create(Prefix + "typeII_isGenericallyRigidInj_two_of_nonCollinear"),
                H("Conditional Type II generic rigidity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A non-collinear injectively rigid planar placement yields an injectively rigid Type II extension."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("typei-7"), DeclarationHandle.Create(Prefix + "exists_nonCollinear_update_perturbation_dim_two"),
                H("A non-collinear continuous perturbation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A continuous one-coordinate perturbation can make three planar placement points non-collinear while avoiding a finite set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("typei-8"), DeclarationHandle.Create(Prefix + "typeII_isGenericallyRigidInj_two"),
                H("Type II preserves injective generic rigidity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Injective generic rigidity in the plane is preserved by every legal Type II Henneberg move."))), DescribeRole.Theorem)), []));
}
