using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorSecondCollisionSliceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorSecondCollisionSlice", H("LatticeSectorSecondCollisionSlice"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorsecondcollisionslice-middleiterate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorSecondCollisionSlice.middleIterate"),
                H("middleIterate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The middleIterate coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectorsecondcollisionslice-clearedmiddleslice"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorSecondCollisionSlice.clearedMiddleSlice"),
                H("clearedMiddleSlice"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The clearedMiddleSlice coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectorsecondcollisionslice-sliceresidueterm"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorSecondCollisionSlice.sliceResidueTerm"),
                H("sliceResidueTerm"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sliceResidueTerm coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectorsecondcollisionslice-actual-collision-slice-finite-residue"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorSecondCollisionSlice.actual_collision_slice_finite_residue"),
                H("actual_collision_slice_finite_residue"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A maximum of actual outer-state truncation bounds over the finite intermediate-mode interval makes the middle Borcherds residue a finite sum. No cutoff over all descendants is used."))), DescribeRole.Theorem))));
}
