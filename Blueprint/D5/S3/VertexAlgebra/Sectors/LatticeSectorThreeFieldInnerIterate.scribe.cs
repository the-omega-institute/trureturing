using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorThreeFieldInnerIterateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorThreeFieldInnerIterate", H("LatticeSectorThreeFieldInnerIterate"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorthreefieldinneriterate-inneriterate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldInnerIterate.innerIterate"),
                H("innerIterate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The innerIterate coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectorthreefieldinneriterate-clearedinneriterate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldInnerIterate.clearedInnerIterate"),
                H("clearedInnerIterate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The clearedInnerIterate coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectorthreefieldinneriterate-actual-three-field-inner-iterate-transport"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldInnerIterate.actual_three_field_inner_iterate_transport"),
                H("actual_three_field_inner_iterate_transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original all-integer Borcherds identity identifies the actual cleared inner canonical iterate with the legal inner substitution of the same six-product numerator, preserving all original witnesses."))), DescribeRole.Theorem))));
}
