using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor;

internal sealed class LocalResiduesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed local residues for the complete middle Taylor equality",
        H("LocalResidues"),
        Blocks(
            Paragraph(Text("The imported collisionTaylor retains the original fractional coefficients. The original orderedResidueWeight data and finite forward Taylor convolution remain here with the complete source/source residue calculation. The signed kernel branches and the coefficient-field data are imported from the canonical binary evaluator.")),
            Paragraph(Text("The completeAB rational field is formed from the ordinary A/B residue before its z mode shift. The entire original ab_complete_remaining_orders conjunction is retained: the finite Laurent monomial representation, the genuine high-weight zero tail, and both remaining Hahn orders of that same field. Its pole bound is L+M+(K-w-1).toNat for arbitrary signed monomials and independent fractional cutoff I. No monomial locality is assumed.")),
            Describe.Lean(
                DescribeId.Create("finite-forward-outer-taylor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.finite_forward_outer_taylor"),
                H("finite_forward_outer_taylor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Consumed original boundary helper for forward_weighted_identity. The source telescope and complete conclusion are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ab-complete-remaining-orders"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.ab_complete_remaining_orders"),
                H("ab_complete_remaining_orders"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Consumed original boundary helper for forward_weighted_identity. The source telescope and complete conclusion are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ab-complete-pole-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues.ab_complete_pole_bound"),
                H("ab_complete_pole_bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Consumed original boundary helper for forward_weighted_identity. The source telescope and complete conclusion are retained."))),
                DescribeRole.Theorem))));
}
