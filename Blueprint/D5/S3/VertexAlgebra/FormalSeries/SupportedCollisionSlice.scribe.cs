using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedCollisionSliceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SupportedCollisionSlice", H("SupportedCollisionSlice"), Blocks(
            Describe.Lean(DescribeId.Create("supportedcollisionslice-modefiber"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedCollisionSlice.modeFiber"),
                H("modeFiber"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed middle coefficient uses the exact integer interval of intermediate canonical modes."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedcollisionslice-mem-modefiber-iff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedCollisionSlice.mem_modeFiber_iff"),
                H("mem_modeFiber_iff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Membership in that mode interval is equivalent to indices in the two finite polynomial fibers."))), DescribeRole.Theorem))));
}
