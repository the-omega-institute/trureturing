using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockPhysicalRescalingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical half-Fock normal field admits signed physical slices and same-mode jets on the actual tensor module.",
        H("Signed Physical Slices and Jets"),
        Blocks(
            Paragraph(Text("The slice at an integer shift is the coefficient reindexing field.coeff (2*mode-shift). "
                + "Its singleton insertion at shift s+2*d+1 is the ordinary normalMinusOne of the canonical jet "
                + "and the slice at s, proved pointwise by the exhaustive signed mode split.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockphysicalrescaling-slice-mode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_mode"),
                H("Slice mode formula"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The physical slice mode is the native field coefficient at -2*mode-shift-2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockphysicalrescaling-jet-mode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalJet_mode"),
                H("Jet mode formula"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The physical jet mode is the canonical same-mode jet current."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockphysicalrescaling-singleton-bridge"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_singletonLinear"),
                H("Singleton physical slice bridge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After fixing the actual tensor vector, the signed finite support partition gives the normalMinusOne bridge."))),
                DescribeRole.Theorem))));
}
