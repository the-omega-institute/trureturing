using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues;

internal sealed class LatticeHalfFockCollisionTaylorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original fractional collision numerator",
        H("LatticeHalfFockCollisionTaylor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("collision-taylor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionTaylor.collisionTaylor"),
                H("collisionTaylor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The Laurent exponents remain integers. The associated-coordinate cocycle is consumed by the finite left Taylor contraction; it does not identify an actual field product by itself."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("associated-taylor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionTaylor.associatedTaylor"),
                H("associatedTaylor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The Laurent exponents remain integers. The associated-coordinate cocycle is consumed by the finite left Taylor contraction; it does not identify an actual field product by itself."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("associated-taylor-cocycle"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionTaylor.associatedTaylor_cocycle"),
                H("associatedTaylor_cocycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The Laurent exponents remain integers. The associated-coordinate cocycle is consumed by the finite left Taylor contraction; it does not identify an actual field product by itself."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fused-residue-weight"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionTaylor.fusedResidueWeight"),
                H("fusedResidueWeight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The Laurent exponents remain integers. The associated-coordinate cocycle is consumed by the finite left Taylor contraction; it does not identify an actual field product by itself."))),
                DescribeRole.Definition))));
}
