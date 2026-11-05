using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedMiddleCollisionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SupportedMiddleCollision", H("SupportedMiddleCollision"), Blocks(
            Describe.Lean(DescribeId.Create("supportedmiddlecollision-middlenativeslice"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedMiddleCollision.middleNativeSlice"),
                H("middleNativeSlice"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The middleNativeSlice coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedmiddlecollision-outerarguments"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedMiddleCollision.outerArguments"),
                H("outerArguments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The outerArguments coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedmiddlecollision-middlenativeslice-extend"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedMiddleCollision.middleNativeSlice_extend"),
                H("middleNativeSlice_extend"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The middleNativeSlice_extend coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedmiddlecollision-outercollision-signed"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedMiddleCollision.outerCollision_signed"),
                H("outerCollision_signed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The outerCollision_signed coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedmiddlecollision-middlearguments"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedMiddleCollision.middleArguments"),
                H("middleArguments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The middleArguments coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedmiddlecollision-outer-inner-substitution"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedMiddleCollision.outer_inner_substitution"),
                H("outer_inner_substitution"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The outer_inner_substitution coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Theorem))));
}
